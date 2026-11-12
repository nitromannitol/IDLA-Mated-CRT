import MatedCRT.FirstPass.Derived.CellLocation
import MatedCRT.FirstPass.Derived.GreenRandomPath

/-!
# The Green function bound through segment paths for the cells of a curve

The bound `MatedCRT.greenFn_le_of_segmentPaths_of_inballs` (Thomson's principle for the
uniformly random segment-path flow through fat cells, BG20 proof of Lemma 5.6) specialised to

* the cells `H^ε_a = η([ε(a-1), εa])` of a continuous curve `η` parametrized by area,
* the killing set `A = V^ε(B_ρ) \ V^ε(∂B_ρ)` (`interiorCellVertices ε η (ball 0 ρ)`),
* the vertex set `S = V^ε(B_ρ)` (`cellVertices ε η (ball 0 ρ)`, assumed finite),
* an edge multiplicity `m` whose edges join intersecting cells.

The hypotheses `hAS`, `hS`, `hdisj`, `hHc`, `hb`, `hsub` and `hrR` of the general bound are
derived here (connectedness of the cells, area parametrization, adjacent vertices have
intersecting cells), with the outer radius `R = ρ + M + ‖u‖`. What remains are the bounds on the
cells meeting `B_ρ` (inscribed discs, diameters, degrees) and the segment paths.

## Main statements

* `MatedCRT.greenFn_interiorCellVertices_le_of_segmentPaths`
-/

open Set Metric MeasureTheory LatticeProb

namespace MatedCRT

/-- **Crude Green function bound for the cells meeting `B_ρ`.** For the cells of a continuous
curve parametrized by area, an edge multiplicity whose edges join intersecting cells, finitely many
cells meeting `B_ρ`, and an interior vertex `x` of `B_ρ`: if every cell meeting `B_ρ` contains a
disc of radius `κ diam H` and has diameter in `[r, M]` and degree at most `Δ`, and the segment
paths from `u` stay in `V^ε(B_ρ)` and end outside `A = V^ε(B_ρ) \ V^ε(∂B_ρ)`, then the Green
function of the walk killed on exiting `A` satisfies
`G_A(a, x) ≤ deg x · ½ Δ ((log₂(M/r) + 1) · 16/κ² + 8 log((ρ + M + ‖u‖)/r)/κ²)`. -/
theorem greenFn_interiorCellVertices_le_of_segmentPaths {μ : Measure ℂ} {η : ℝ → ℂ} {ε ρ : ℝ}
    {m : ℤ → ℤ → ℕ} (hη : Continuous η) (hap : IsAreaParametrized μ η) (hε : 0 < ε)
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hsymm : ∀ a b, m a b = m b a)
    (hadj : ∀ j k, m k j ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hfin : (cellVertices ε η (ball 0 ρ)).Finite) {x : ℤ}
    (hx : x ∈ interiorCellVertices ε η (ball 0 ρ)) {c : ℤ → ℂ} {u : ℂ} {ℓ κ r M Δ : ℝ}
    (hκ : 0 < κ) (hr : 0 < r) (hrM : r ≤ M) (hΔ : 0 ≤ Δ)
    (hball : ∀ a ∈ cellVertices ε η (ball 0 ρ),
      ball (c a) (κ * diam (cell ε η a)) ⊆ cell ε η a)
    (hlo : ∀ a ∈ cellVertices ε η (ball 0 ρ), r ≤ diam (cell ε η a))
    (hhi : ∀ a ∈ cellVertices ε η (ball 0 ρ), diam (cell ε η a) ≤ M)
    (hdeg : ∀ a ∈ cellVertices ε η (ball 0 ρ), (mdeg m a : ℝ) ≤ Δ)
    {Y : Finset ℤ} {F : Finset ℤ → List ℤ} (hF : ∀ T : Finset ℤ, ∀ a ∈ F T, a ∈ T)
    (hnd : ∀ θ, (segmentPath u ℓ (cell ε η) Y F θ).Nodup)
    (hchain : ∀ θ, (segmentPath u ℓ (cell ε η) Y F θ).IsChain fun a b => m a b ≠ 0)
    (hpath : ∀ θ, ∃ p, segmentPath u ℓ (cell ε η) Y F θ = x :: p ∧
      (∀ v ∈ x :: p, v ∈ cellVertices ε η (ball 0 ρ)) ∧
      (x :: p).getLast (List.cons_ne_nil x p) ∉ interiorCellVertices ε η (ball 0 ρ))
    (a : ℤ) :
    greenFn m (interiorCellVertices ε η (ball 0 ρ)) a x ≤ (mdeg m x : ℝ) * ((1 / 2) * (Δ *
      ((Real.logb 2 (M / r) + 1) * (16 / κ ^ 2) +
        8 * Real.log ((ρ + M + ‖u‖) / r) / κ ^ 2))) := by
  have hIV : interiorCellVertices ε η (ball 0 ρ) ⊆ cellVertices ε η (ball 0 ρ) := sdiff_subset
  have hfinI := hfin.subset hIV
  have hS : ∀ {a}, a ∈ hfin.toFinset ↔ a ∈ cellVertices ε η (ball 0 ρ) := hfin.mem_toFinset
  have hA : ∀ {a}, a ∈ hfinI.toFinset ↔ a ∈ interiorCellVertices ε η (ball 0 ρ) :=
    hfinI.mem_toFinset
  have hρ : 0 ≤ ρ := by
    obtain ⟨y, -, hy⟩ := hx.1
    exact dist_nonneg.trans (mem_ball.1 hy).le
  have hsub : ∀ a ∈ hfin.toFinset, cell ε η a ⊆ closedBall u (ρ + M + ‖u‖) := by
    intro a ha y hy
    have ha' := hS.1 ha
    have h1 := cell_subset_closedBall_of_inter_ball hη ha' hy
    rw [mem_closedBall] at h1 ⊢
    have h2 : dist (0 : ℂ) u = ‖u‖ := by rw [dist_comm, dist_zero_right]
    have h3 := dist_triangle y 0 u
    linarith [hhi a ha']
  rw [← hfinI.coe_toFinset]
  refine greenFn_le_of_segmentPaths_of_inballs (c := c) hlf hcons hsymm
    (fun a ha => hS.2 (hIV (hA.1 ha)))
    (fun a ha b hb => hS.2 (mem_cellVertices_of_mult_ne_zero hη hadj (hA.1 ha) hb))
    (hA.2 hx) hκ hr hrM (by linarith [norm_nonneg u]) hΔ
    (pairwiseDisjoint_inball_cell hap hε fun k hk => hball k (hS.1 (Finset.mem_coe.1 hk)))
    (fun y _ => (isCompact_Icc.image hη).isClosed) (fun a _ => isBounded_cell hη a)
    (fun a ha => hball a (hS.1 ha)) (fun a ha => hlo a (hS.1 ha)) (fun a ha => hhi a (hS.1 ha))
    hsub (fun a ha => hdeg a (hS.1 ha)) hF hnd hchain (fun θ => ?_) a
  obtain ⟨p, hp, hv, hl⟩ := hpath θ
  exact ⟨p, hp, fun v hv' => hS.2 (hv v hv'), fun h => hl (hA.1 h)⟩

end MatedCRT
