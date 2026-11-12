import MatedCRT.FirstPass.Derived.GreenCellSegmentPaths
import LatticeProb.Network.SegmentPathFlowAE

/-!
# The killed Green function bounded by segment paths of almost every direction

The expected crossing flow of the uniformly random segment path sees the path only through the
probabilities of its values, so the self-avoidance, chain and unit-divergence hypotheses of the
method of random segment paths need only hold for almost every direction `θ` of the uniform
measure on `(0, 2π]` (`LatticeProb.SegmentPathFlowAE`). This matters for the cells of
space-filling SLE: the segment from `u` in direction `θ` meets the cells in a regular way only
off the null set of directions of the points where several cells touch.

## Main statements

* `MatedCRT.greenFn_le_of_segmentPaths_of_inballs_ae`: the crude bound for the killed Green
  function of `greenFn_le_of_segmentPaths_of_inballs` (BG20, lem-eff-res-upper, disjoint inballs)
  with `hnd`, `hchain`, `hpath` for almost every direction.
* `MatedCRT.greenFn_interiorCellVertices_le_of_segmentPaths_ae`: its specialization to the cells
  `H^ε_a = η([ε(a-1), εa])` of a continuous curve parametrized by area, the killing set
  `V^ε(B_ρ) \ V^ε(∂B_ρ)` and the vertex set `V^ε(B_ρ)`.
-/

namespace MatedCRT

open Set Finset Function Metric MeasureTheory LatticeProb

variable {m : ℤ → ℤ → ℕ}

/-- **Crude bound for the killed Green function by random segment paths, almost every
direction.** The bound of `greenFn_le_of_segmentPaths_of_inballs` when the selected paths are
nodup chains of the graph from `x`, staying in `S` and ending outside `A`, only for almost every
direction `θ`. -/
theorem greenFn_le_of_segmentPaths_of_inballs_ae (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) (hsymm : ∀ a b, m a b = m b a)
    {A S Y : Finset ℤ} (hAS : A ⊆ S) (hS : ∀ a ∈ A, ∀ b, m a b ≠ 0 → b ∈ S) {x : ℤ}
    (hx : x ∈ A) {H : ℤ → Set ℂ} {c : ℤ → ℂ} {u : ℂ} {ρ κ r M R Δ : ℝ} (hκ : 0 < κ)
    (hr : 0 < r) (hrM : r ≤ M) (hrR : r ≤ R) (hΔ : 0 ≤ Δ)
    (hdisj : (S : Set ℤ).PairwiseDisjoint fun a => ball (c a) (κ * diam (H a)))
    (hHc : ∀ y ∈ Y, IsClosed (H y)) (hb : ∀ a ∈ S, Bornology.IsBounded (H a))
    (hball : ∀ a ∈ S, ball (c a) (κ * diam (H a)) ⊆ H a)
    (hlo : ∀ a ∈ S, r ≤ diam (H a)) (hhi : ∀ a ∈ S, diam (H a) ≤ M)
    (hsub : ∀ a ∈ S, H a ⊆ closedBall u R)
    (hdeg : ∀ a ∈ S, (mdeg m a : ℝ) ≤ Δ)
    {F : Finset ℤ → List ℤ} (hF : ∀ T : Finset ℤ, ∀ a ∈ F T, a ∈ T)
    (hnd : ∀ᵐ θ ∂uniformDirection, (segmentPath u ρ H Y F θ).Nodup)
    (hchain : ∀ᵐ θ ∂uniformDirection,
      (segmentPath u ρ H Y F θ).IsChain fun a b => m a b ≠ 0)
    (hpath : ∀ᵐ θ ∂uniformDirection, ∃ p, segmentPath u ρ H Y F θ = x :: p ∧
      (∀ v ∈ x :: p, v ∈ S) ∧ (x :: p).getLast (List.cons_ne_nil x p) ∉ A) (a : ℤ) :
    greenFn m (A : Set ℤ) a x ≤ (mdeg m x : ℝ) * ((1 / 2) * (Δ *
      ((Real.logb 2 (M / r) + 1) * (16 / κ ^ 2) + 8 * Real.log (R / r) / κ ^ 2))) := by
  have hchain' : ∀ᵐ θ ∂uniformDirection,
      (segmentPath u ρ H Y F θ).IsChain fun a b => (m a b : ℝ) ≠ 0 := by
    filter_upwards [hchain] with θ hθ
    exact hθ.imp fun ⦃_ _⦄ h => by exact_mod_cast h
  have hR' : ∀ a b : ℤ, (m a b : ℝ) ≠ 0 → (m b a : ℝ) ≠ 0 := fun a b h => by
    rwa [hsymm b a]
  refine (greenFn_le_mdeg_mul_flowEnergy hlf hcons hsymm hAS hS hx
    (θ := segmentPathFlow u ρ H Y F) (fun a b => segmentPathFlow_antisymm a b)
    (fun a b h0 => segmentPathFlow_eq_zero_of_not_rel_ae hR' hchain' (by simp [h0]))
    (sum_segmentPathFlow_eq_ite_of_path_ae hHc hpath) a).trans ?_
  have hE := sum_sum_sq_div_le_of_fatInballs (θ := segmentPathFlow u ρ H Y F)
    (w := fun a b => (m a b : ℝ)) hκ hr hrM hrR hΔ hdisj hb hball hlo hhi hsub
    (fun _ _ => Nat.cast_nonneg _)
    (fun a b h => by
      have h' : m a b ≠ 0 := fun h0 =>
        h (segmentPathFlow_eq_zero_of_not_rel_ae hR' hchain' (by simp [h0]))
      simpa using Nat.one_le_iff_ne_zero.2 h')
    (fun a ha => show ∑ b ∈ S, (m a b : ℝ) ≤ Δ by
      rw [← Nat.cast_sum]
      exact (Nat.cast_le.2 (sum_le_mdeg hlf S a)).trans (hdeg a ha))
    (fun a _ b _ => abs_segmentPathFlow_le_one_ae hHc hnd a b)
    (fun a ha hfar b _ => abs_segmentPathFlow_le_diam_div_infDist_ae hHc hnd
      (fun θ a h => mem_segmentDirections_of_mem_segmentPath hF h) (hb a ha)
      (diam_nonneg.trans_lt hfar) b)
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE (by norm_num))
    (Nat.cast_nonneg _)

/-- **Crude Green function bound for the cells meeting `B_ρ`, almost every direction.** The bound
of `greenFn_interiorCellVertices_le_of_segmentPaths` when the segment paths from `u` are nodup
chains of the graph from `x`, stay in `V^ε(B_ρ)` and end outside `V^ε(B_ρ) \ V^ε(∂B_ρ)` only for
almost every direction `θ`. -/
theorem greenFn_interiorCellVertices_le_of_segmentPaths_ae {μ : Measure ℂ} {η : ℝ → ℂ}
    {ε ρ : ℝ} (hη : Continuous η) (hap : IsAreaParametrized μ η) (hε : 0 < ε)
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
    (hnd : ∀ᵐ θ ∂uniformDirection, (segmentPath u ℓ (cell ε η) Y F θ).Nodup)
    (hchain : ∀ᵐ θ ∂uniformDirection,
      (segmentPath u ℓ (cell ε η) Y F θ).IsChain fun a b => m a b ≠ 0)
    (hpath : ∀ᵐ θ ∂uniformDirection, ∃ p, segmentPath u ℓ (cell ε η) Y F θ = x :: p ∧
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
  refine greenFn_le_of_segmentPaths_of_inballs_ae (c := c) hlf hcons hsymm
    (fun a ha => hS.2 (hIV (hA.1 ha)))
    (fun a ha b hb => hS.2 (mem_cellVertices_of_mult_ne_zero hη hadj (hA.1 ha) hb))
    (hA.2 hx) hκ hr hrM (by linarith [norm_nonneg u]) hΔ
    (pairwiseDisjoint_inball_cell hap hε fun k hk => hball k (hS.1 (Finset.mem_coe.1 hk)))
    (fun y _ => (isCompact_Icc.image hη).isClosed) (fun a _ => isBounded_cell hη a)
    (fun a ha => hball a (hS.1 ha)) (fun a ha => hlo a (hS.1 ha)) (fun a ha => hhi a (hS.1 ha))
    hsub (fun a ha => hdeg a (hS.1 ha)) hF hnd hchain ?_ a
  filter_upwards [hpath] with θ hθ
  obtain ⟨p, hp, hv, hl⟩ := hθ
  exact ⟨p, hp, fun v hv' => hS.2 (hv v hv'), fun h => hl (hA.1 h)⟩

end MatedCRT
