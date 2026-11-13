import MatedCRT.Defs.Setting

/-!
# Measure-theoretic and geometric steps of the exit-time lower tail (proof of BG20 Lemma 6.9)

The estimate (6.32) of BG20 (arXiv:2003.10320, Lemma 6.9) is proved on the intersection of three events:
the event of the uniform-start invariance principle (N4, probability at least `1 - θ/2`), the event that all
cells meeting `B_R(0)` have diameter at most `c` (probability at least `1 - θ/2`), and the almost sure event that
consecutive cells of the walk intersect. This file collects the steps of that assembly which do not involve
the comparison of step times:

* `vertexPoint_mem_closedBall_of_mem_cellVertices`: on the cell-size event, a vertex whose cell meets
  `B_{ρ-δ}(0)` is embedded in `closedBall 0 ρ` once `c ≤ δ`, so that N4 applies to it;
* `measure_compl_le_of_forall_good`, `exists_eps_measure_compl_le`: the union bound over the two
  high-probability events and the almost sure event, and the choice `ε₀ := min ε₁ ε₂`;
* `compl_setOf_forall_srwLaw_le_eq_empty`: when the bound `ψ₀(δ)` is at least `1` the estimate holds
  trivially, since the walk laws are probability measures.
-/

namespace MatedCRT.ExitTailAssembly

open MeasureTheory Set Metric
open scoped ENNReal

/-- **Starting vertices of the walk lie in `closedBall 0 ρ`.** If the cell of `x` meets `B_{ρ-δ}(0)` and every
cell meeting `B_R(0) ⊇ B_{ρ-δ}(0)` has diameter at most `c ≤ δ`, then `η(εx) ∈ closedBall 0 ρ`. -/
theorem vertexPoint_mem_closedBall_of_mem_cellVertices {ε c δ ρ R : ℝ} {η : ℝ → ℂ}
    (hη : Continuous η) (hε : 0 ≤ ε) {x : ℤ} (hx : x ∈ cellVertices ε η (ball 0 (ρ - δ)))
    (hρR : ρ - δ ≤ R)
    (hcell : ∀ k : ℤ, (cell ε η k ∩ ball 0 R).Nonempty → diam (cell ε η k) ≤ c) (hcδ : c ≤ δ) :
    vertexPoint ε η x ∈ closedBall (0 : ℂ) ρ := by
  obtain ⟨z, hzc, hzb⟩ := hx
  have hzR : z ∈ ball (0 : ℂ) R := ball_subset_ball hρR hzb
  have hbdd : Bornology.IsBounded (cell ε η x) :=
    (isCompact_Icc.image hη).isBounded
  have hv : vertexPoint ε η x ∈ cell ε η x :=
    ⟨ε * x, ⟨mul_le_mul_of_nonneg_left (by linarith) hε, le_rfl⟩, rfl⟩
  have hd : dist (vertexPoint ε η x) z ≤ c :=
    (dist_le_diam_of_mem hbdd hv hzc).trans (hcell x ⟨z, hzc, hzR⟩)
  rw [mem_closedBall, dist_zero_right]
  rw [mem_ball, dist_zero_right] at hzb
  calc ‖vertexPoint ε η x‖ ≤ ‖z‖ + dist (vertexPoint ε η x) z := by
        rw [dist_eq_norm]; exact norm_le_insert' _ _
    _ ≤ ρ := by linarith

/-- **Union bound over two high-probability events and an almost sure event.** If `T` holds on
`G₁ ∩ G₂ ∩ {G₃}` and `G₃` holds almost surely, then `P Tᶜ ≤ P G₁ᶜ + P G₂ᶜ`. -/
theorem measure_compl_le_of_forall_good {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T G₁ G₂ : Set Ω} {G₃ : Ω → Prop} (hG₃ : ∀ᵐ ω ∂P, G₃ ω)
    (h : ∀ ω ∈ G₁, ω ∈ G₂ → G₃ ω → ω ∈ T) {θ₁ θ₂ : ℝ≥0∞} (h₁ : P G₁ᶜ ≤ θ₁) (h₂ : P G₂ᶜ ≤ θ₂) :
    P Tᶜ ≤ θ₁ + θ₂ := by
  have hN : P {ω | ¬ G₃ ω} = 0 := ae_iff.mp hG₃
  have hsub : Tᶜ ⊆ (G₁ᶜ ∪ G₂ᶜ) ∪ {ω | ¬ G₃ ω} := by
    intro ω hω
    by_cases h1 : ω ∈ G₁
    · by_cases h2 : ω ∈ G₂
      · exact Or.inr fun h3 => hω (h ω h1 h2 h3)
      · exact Or.inl (Or.inr h2)
    · exact Or.inl (Or.inl h1)
  calc P Tᶜ ≤ P ((G₁ᶜ ∪ G₂ᶜ) ∪ {ω | ¬ G₃ ω}) := measure_mono hsub
    _ ≤ P (G₁ᶜ ∪ G₂ᶜ) + P {ω | ¬ G₃ ω} := measure_union_le _ _
    _ ≤ P G₁ᶜ + P G₂ᶜ + 0 := by rw [hN]; gcongr; exact measure_union_le _ _
    _ ≤ θ₁ + θ₂ := by rw [add_zero]; exact add_le_add h₁ h₂

/-- **Choice of `ε₀`.** If `T ε` holds on `G₁ ε ∩ G₂ ε ∩ {G₃}` for every `ε > 0`, `G₃` holds almost surely,
and `P (G_i ε)ᶜ ≤ θ/2` for `ε ∈ (0, ε_i)`, then `P (T ε)ᶜ ≤ θ` for `ε ∈ (0, min ε₁ ε₂)`. -/
theorem exists_eps_measure_compl_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T G₁ G₂ : ℝ → Set Ω} {G₃ : Ω → Prop} (hG₃ : ∀ᵐ ω ∂P, G₃ ω)
    (h : ∀ ε : ℝ, 0 < ε → ∀ ω ∈ G₁ ε, ω ∈ G₂ ε → G₃ ω → ω ∈ T ε) {θ : ℝ} (hθ : 0 ≤ θ)
    (h₁ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → P (G₁ ε)ᶜ ≤ ENNReal.ofReal (θ / 2))
    (h₂ : ∃ ε₂ : ℝ, 0 < ε₂ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₂ → P (G₂ ε)ᶜ ≤ ENNReal.ofReal (θ / 2)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → P (T ε)ᶜ ≤ ENNReal.ofReal θ := by
  obtain ⟨ε₁, hε₁, h₁⟩ := h₁
  obtain ⟨ε₂, hε₂, h₂⟩ := h₂
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun ε hε hεlt => ?_⟩
  have hθ2 : 0 ≤ θ / 2 := by linarith
  calc P (T ε)ᶜ ≤ ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) :=
        measure_compl_le_of_forall_good P hG₃ (h ε hε)
          (h₁ ε hε (hεlt.trans_le (min_le_left _ _))) (h₂ ε hε (hεlt.trans_le (min_le_right _ _)))
    _ = ENNReal.ofReal θ := by rw [← ENNReal.ofReal_add hθ2 hθ2, add_halves]

/-- **The trivial range of (6.32).** When `1 ≤ ψ`, every walk probability is at most `ψ`, so the event of the
estimate is everything. -/
theorem compl_setOf_forall_srwLaw_le_eq_empty {Ω : Type*} {V : Ω → Set ℤ}
    {m : Ω → ℤ → ℤ → ℕ} {E : Ω → ℤ → Set (ℕ → ℤ)} {ψ : ℝ} (hψ : 1 ≤ ψ) :
    {ω | ∀ x ∈ V ω, srwLaw (m ω) x (E ω x) ≤ ENNReal.ofReal ψ}ᶜ = ∅ := by
  ext ω
  refine ⟨fun hω => (hω fun x _ => ?_).elim, fun h => h.elim⟩
  calc srwLaw (m ω) x (E ω x) ≤ 1 := prob_le_one
    _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
    _ ≤ ENNReal.ofReal ψ := ENNReal.ofReal_le_ofReal hψ

end MatedCRT.ExitTailAssembly
