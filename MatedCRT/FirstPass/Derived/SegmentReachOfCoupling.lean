import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.SafeCellChain
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.EquicontinuityLemmas
import MatedCRT.FirstPass.Derived.SegmentBallsOfCoupling
import MatedCRT.FirstPass.S5c.GreenUpper

/-!
# Segment reachability in every direction

For a valid mated-CRT environment, almost surely, for every mesh `ε > 0` and every vertex `x`
of `V^ε(B_ρ(0)) \ V^ε(∂B_ρ(0))`, there is a base point `u` in the cell of `x` such that, for
EVERY direction `θ`, the cells hit by the segment `[u, u + 2 e^{iθ}]` and meeting `B_ρ(0)`
contain a path of `𝒢^ε` from `x` to a vertex of `V^ε(∂B_ρ(0))`.

The argument is deterministic once three almost sure properties of the environment hold: the
cells meeting a compact preconnected set are connected through any vertex set containing them
(`MatedCRTEnv.IsValid.ae_reachable_in_safe_cell_cover`), the curve is proper, and the curve is
parametrized by area (continuous and onto). Follow the segment from `u` until its exit point
`p` from `B_ρ(0)`; a cell through `p` meets the part of the segment inside the ball, and the
safe-cover connectivity applied to the initial piece of the segment ending in that cell gives
the path.

Consequently the reachability input of `greenFunctionCrudeBoundStmt_of_reachableAE` holds with
radius `1` for every valid environment, and the crude Green function bound (Lemma 2.15) follows
from the cell size estimate and the degree bound alone.
-/

open Set Metric MeasureTheory Filter Topology HarmonicBalls Complex

namespace MatedCRT

/-- A path in the subgraph of `adjGraph m` induced by `U` gives a chain of nonzero edge counts
whose vertices after the first lie in `U`, for symmetric `m`. -/
theorem reflTransGen_of_reachable_induce {m : ℤ → ℤ → ℕ} (hm : ∀ a b, m a b = m b a)
    {U : Set ℤ} {j k : ℤ} {hj : j ∈ U} {hk : k ∈ U}
    (h : ((adjGraph m).induce U).Reachable ⟨j, hj⟩ ⟨k, hk⟩) :
    Relation.ReflTransGen (fun a c => c ∈ U ∧ m a c ≠ 0) j k := by
  have h' := (SimpleGraph.reachable_iff_reflTransGen _ _).1 h
  refine Relation.ReflTransGen.lift (p := fun a c => c ∈ U ∧ m a c ≠ 0) Subtype.val ?_ _ _ h'
  intro a c hac
  simp only [SimpleGraph.induce_adj, adjGraph, SimpleGraph.fromRel_adj] at hac
  refine ⟨c.2, ?_⟩
  rcases hac.2 with h1 | h1
  · exact h1
  · rwa [hm]

/-- **Segment reachability from a given point of a cell.** Let `η` be continuous, proper and
onto, and assume that the cells meeting any compact preconnected set `K` are mutually reachable
in the subgraph of `adjGraph m` induced by any vertex set containing them. Let `x` be a vertex and
`u ∈ H^ε_x ∩ B_ρ(0)`. Then there is a finite set `Y` such that, for every direction `θ`, `x` is hit
by the segment `[u, u + 2 e^{iθ}]`, and some vertex `c ∉ V^ε(B_ρ(0)) \ V^ε(∂B_ρ(0))` is reachable
from `x` in the subgraph induced by the vertices hit by the segment whose cells meet `B_ρ(0)`. -/
theorem segmentReach_of_safeCover_from {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {η : ℝ → ℂ} (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hsurj : Function.Surjective η) {m : ℤ → ℤ → ℕ}
    (hcover : ∀ K : Set ℂ, IsPreconnected K → IsCompact K → ∀ U : Set ℤ,
      ∀ (hsafe : ∀ j, (K ∩ cell ε η j).Nonempty → j ∈ U), ∀ j k : ℤ,
      ∀ (hj : (K ∩ cell ε η j).Nonempty) (hk : (K ∩ cell ε η k).Nonempty),
      ((adjGraph m).induce U).Reachable ⟨j, hsafe j hj⟩ ⟨k, hsafe k hk⟩)
    {x : ℤ} {u : ℂ} (hux : u ∈ cell ε η x) (hub : u ∈ ball (0 : ℂ) ρ) :
    ∃ Y : Finset ℤ, ∀ θ : ℝ,
      x ∈ LatticeProb.hitFinset Y (fun y => LatticeProb.segmentDirections u 2 (cell ε η y)) θ ∧
      ∃ c ∉ interiorCellVertices ε η (ball 0 ρ),
        ∃ (hxU : x ∈ {v | v ∈ LatticeProb.hitFinset Y
            (fun y => LatticeProb.segmentDirections u 2 (cell ε η y)) θ ∧
              v ∈ cellVertices ε η (ball 0 ρ)})
          (hcU : c ∈ {v | v ∈ LatticeProb.hitFinset Y
            (fun y => LatticeProb.segmentDirections u 2 (cell ε η y)) θ ∧
              v ∈ cellVertices ε η (ball 0 ρ)}),
          ((adjGraph m).induce {v | v ∈ LatticeProb.hitFinset Y
            (fun y => LatticeProb.segmentDirections u 2 (cell ε η y)) θ ∧
              v ∈ cellVertices ε η (ball 0 ρ)}).Reachable ⟨x, hxU⟩ ⟨c, hcU⟩ := by
  have hu : ‖u‖ < ρ := mem_ball_zero_iff.1 hub
  let Y : Finset ℤ := (S5c.cellVertices_ball_finite hη hp hε (0 : ℂ) 3).toFinset
  refine ⟨Y, fun θ => ?_⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ → ℂ, σ = fun t : ℝ => u + (t : ℂ) * exp (θ * I) := ⟨_, rfl⟩
  have hσapp : ∀ t : ℝ, σ t = u + (t : ℂ) * exp (θ * I) := fun t => by rw [hσ]
  have hσc : Continuous σ := by rw [hσ]; fun_prop
  have hσ0 : σ 0 = u := by rw [hσapp]; simp
  -- the cells met by the segment inside `B_3(0)` are hit
  have hhit : ∀ τ ∈ Icc (0 : ℝ) 2, ∀ j, σ τ ∈ cell ε η j → ‖σ τ‖ < 3 →
      j ∈ LatticeProb.hitFinset Y
        (fun y => LatticeProb.segmentDirections u 2 (cell ε η y)) θ := by
    intro τ hτ j hj h3
    rw [LatticeProb.mem_hitFinset]
    refine ⟨(Set.Finite.mem_toFinset _).2 ⟨σ τ, hj, mem_ball_zero_iff.2 h3⟩, τ, hτ, ?_⟩
    rw [← hσapp]
    exact hj
  refine ⟨hhit 0 ⟨le_rfl, zero_le_two⟩ x (hσ0 ▸ hux) (by rw [hσ0]; linarith), ?_⟩
  -- the exit time `t₀ ∈ (0, 2]` from the ball
  have hf2 : ρ ≤ ‖σ 2‖ := by
    have h2 : ‖((2 : ℝ) : ℂ) * exp (θ * I)‖ = 2 := by
      rw [norm_mul, norm_exp_ofReal_mul_I]; simp
    have hsub : σ 2 - u = ((2 : ℝ) : ℂ) * exp (θ * I) := by rw [hσapp]; ring
    have := norm_sub_le (σ 2) u
    rw [hsub, h2] at this
    linarith
  obtain ⟨t₀, ht₀, hpt⟩ : ∃ t₀ ∈ Icc (0 : ℝ) 2, ‖σ t₀‖ = ρ :=
    intermediate_value_Icc zero_le_two hσc.norm.continuousOn
      ⟨show ‖σ 0‖ ≤ ρ by rw [hσ0]; exact hu.le, hf2⟩
  have ht₀pos : 0 < t₀ := by
    rcases ht₀.1.eq_or_lt with h | h
    · rw [← h, hσ0] at hpt; linarith
    · exact h
  -- before the exit time the segment stays in the open ball
  have hinside : ∀ τ ∈ Ico (0 : ℝ) t₀, ‖σ τ‖ < ρ := by
    intro τ hτ
    have hint : u ∈ interior (ball (0 : ℂ) ρ) := by rw [isOpen_ball.interior_eq]; exact hub
    have hcl : σ t₀ ∈ closure (ball (0 : ℂ) ρ) := by
      rw [closure_ball 0 hρ.ne']; exact mem_closedBall_zero_iff.2 hpt.le
    have hmem := (convex_ball (0 : ℂ) ρ).combo_interior_closure_mem_interior hint hcl
      (a := 1 - τ / t₀) (b := τ / t₀) (by rw [sub_pos, div_lt_one ht₀pos]; exact hτ.2)
      (div_nonneg hτ.1 ht₀pos.le) (by ring)
    rw [isOpen_ball.interior_eq] at hmem
    have ht₀C : (t₀ : ℂ) ≠ 0 := by exact_mod_cast ht₀pos.ne'
    have heq : (1 - τ / t₀) • u + (τ / t₀) • σ t₀ = σ τ := by
      rw [hσapp, hσapp, Complex.real_smul, Complex.real_smul]
      push_cast
      field_simp
      ring
    rw [heq] at hmem
    exact mem_ball_zero_iff.1 hmem
  -- a cell through the exit point that meets the segment inside the ball
  have hpcl : σ t₀ ∈ closure (σ '' Ico 0 t₀) := by
    apply image_closure_subset_closure_image hσc
    rw [closure_Ico ht₀pos.ne]
    exact mem_image_of_mem σ ⟨ht₀pos.le, le_rfl⟩
  obtain ⟨c, ⟨q, hqc, s, hs, rfl⟩, hpc⟩ :=
    Tightness.exists_mem_cellVertices_of_mem_closure hη hp hsurj hε hpcl
  have hcF : c ∈ cellVertices ε η (frontier (ball (0 : ℂ) ρ)) := by
    refine ⟨σ t₀, hpc, ?_⟩
    rw [frontier_ball 0 hρ.ne']
    exact mem_sphere_zero_iff_norm.2 hpt
  refine ⟨c, fun h => h.2 hcF, ?_⟩
  -- connect the cells met by the initial piece `σ '' [0, s]` of the segment
  let U' : Set ℤ := {c | c ∈ LatticeProb.hitFinset Y
      (fun y => LatticeProb.segmentDirections u 2 (cell ε η y)) θ ∧
    c ∈ cellVertices ε η (ball 0 ρ)}
  have hsafe : ∀ j, (σ '' Icc 0 s ∩ cell ε η j).Nonempty → j ∈ U' := by
    rintro j ⟨w, ⟨τ, hτ, rfl⟩, hwj⟩
    have hτ' : τ ∈ Ico 0 t₀ := ⟨hτ.1, hτ.2.trans_lt hs.2⟩
    have hlt := hinside τ hτ'
    exact ⟨hhit τ ⟨hτ.1, hτ'.2.le.trans ht₀.2⟩ j hwj (by linarith),
      σ τ, hwj, mem_ball_zero_iff.2 hlt⟩
  have hj : (σ '' Icc 0 s ∩ cell ε η x).Nonempty := ⟨u, ⟨0, ⟨le_rfl, hs.1⟩, hσ0⟩, hux⟩
  have hk : (σ '' Icc 0 s ∩ cell ε η c).Nonempty := ⟨σ s, ⟨s, ⟨hs.1, le_rfl⟩, rfl⟩, hqc⟩
  exact ⟨_, _, hcover (σ '' Icc 0 s) (isPreconnected_Icc.image σ hσc.continuousOn)
    (isCompact_Icc.image hσc) U' hsafe x c hj hk⟩

/-- **Segment reachability for a fixed curve.** Let `η` be continuous, proper and onto, `m`
symmetric, and assume that the cells meeting any compact preconnected set `K` are mutually
reachable in the subgraph of `adjGraph m` induced by any vertex set containing them. Then for
every `x ∈ V^ε(B_ρ(0)) \ V^ε(∂B_ρ(0))` there are `u` with `‖u‖ ≤ 1`, a length `ℓ` and a
finite set `Y` such that, for every direction `θ`, `x` is hit by the segment
`[u, u + ℓ e^{iθ}]` and some vertex of `V^ε(∂B_ρ(0))` is reached from `x` by a chain of
edges whose vertices are hit by the segment and meet `B_ρ(0)`. -/
theorem segmentReach_of_safeCover {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {η : ℝ → ℂ} (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hsurj : Function.Surjective η)
    {m : ℤ → ℤ → ℕ} (hm : ∀ a b, m a b = m b a)
    (hcover : ∀ K : Set ℂ, IsPreconnected K → IsCompact K → ∀ U : Set ℤ,
      ∀ (hsafe : ∀ j, (K ∩ cell ε η j).Nonempty → j ∈ U), ∀ j k : ℤ,
      ∀ (hj : (K ∩ cell ε η j).Nonempty) (hk : (K ∩ cell ε η k).Nonempty),
      ((adjGraph m).induce U).Reachable ⟨j, hsafe j hj⟩ ⟨k, hsafe k hk⟩)
    {x : ℤ} (hx : x ∈ interiorCellVertices ε η (ball 0 ρ)) :
    ∃ (u : ℂ) (ℓ : ℝ) (Y : Finset ℤ), ‖u‖ ≤ 1 ∧ ∀ θ : ℝ,
      x ∈ LatticeProb.hitFinset Y (fun y => LatticeProb.segmentDirections u ℓ (cell ε η y)) θ ∧
      ∃ b ∉ interiorCellVertices ε η (ball 0 ρ), Relation.ReflTransGen
        (fun a c => (c ∈ LatticeProb.hitFinset Y
            (fun y => LatticeProb.segmentDirections u ℓ (cell ε η y)) θ ∧
          c ∈ cellVertices ε η (ball 0 ρ)) ∧ m a c ≠ 0) x b := by
  obtain ⟨u, hux, hub⟩ := hx.1
  obtain ⟨Y, hY⟩ := segmentReach_of_safeCover_from hε hρ hρ1 hη hp hsurj hcover hux hub
  refine ⟨u, 2, Y, (mem_ball_zero_iff.1 hub).le.trans hρ1.le, fun θ => ?_⟩
  obtain ⟨hxθ, c, hc, _, _, hreach⟩ := hY θ
  exact ⟨hxθ, c, hc, reflTransGen_of_reachable_induce hm hreach⟩

/-- Almost surely, for every mesh `ε > 0`, the segment reachability event holds with radius `1`. -/
theorem MatedCRTEnv.IsValid.ae_mem_segmentReachEvent {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ω ∈ S.segmentReachEvent ρ 1 ε := by
  filter_upwards [hS.ae_reachable_in_safe_cell_cover, hS.ae_tendsto_cocompact,
    hS.isAreaParametrized] with ω hcov hp harea
  intro ε hε x hx
  exact segmentReach_of_safeCover hε hρ hρ1 harea.1 hp harea.2.2.1 (S.mult_symm ε ω)
    (hcov ε hε) hx

/-- The almost-every-direction segment reachability event at radius `1` holds with
polynomially high probability (in fact almost surely, for every mesh). -/
theorem MatedCRTEnv.IsValid.polyHighProb_segmentReachEventAE {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    PolyHighProb S.P (S.segmentReachEventAE ρ 1) := by
  refine ⟨1, one_pos, 0, 1, one_pos, fun r hr _ => ?_⟩
  have h0 : S.P (S.segmentReachEventAE ρ 1 r)ᶜ = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 (hS.ae_mem_segmentReachEvent hρ hρ1))
    exact fun h => hω (S.segmentReachEvent_subset_segmentReachEventAE ρ 1 r (h r hr))
  simp [h0]

/-- **Lemma 2.15 from the cell size estimate and the degree bound.** The segment-ball estimate
and the segment reachability event hold for every valid environment, so the crude Green
function bound follows from `CellSizeEstimateStmt` and `DegreeBoundInput` alone. -/
theorem greenFunctionCrudeBoundStmt_of_cellSize_of_degreeBound {𝒮 : SpaceFillingSLEModel}
    (hcell : CellSizeEstimateStmt 𝒮) (hdeg : DegreeBoundInput 𝒮) :
    GreenFunctionCrudeBoundStmt 𝒮 :=
  greenFunctionCrudeBoundStmt_of_reachableAE hcell hdeg
    (fun _ _ _ _ hρ hρ1 _ _ _ hS => ⟨1, zero_le_one, hS.polyHighProb_segmentReachEventAE hρ hρ1⟩)

end MatedCRT
