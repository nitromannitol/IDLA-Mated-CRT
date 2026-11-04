import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.PointwiseConvergence

/-! Finite-net criterion for uniform convergence in probability. -/

namespace MatedCRT

open Set Filter Topology MeasureTheory _root_.HarmonicBalls
open scoped ENNReal

/-- Pointwise convergence in probability upgrades to uniform convergence if,
with high probability, finitely many common anchors approximate both functions. -/
theorem uniformInProbability_of_finite_anchors
    {Ω α : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : Set α)
    (F : ℝ → Ω → α → ℝ) (U : Ω → α → ℝ)
    (hpoint : ∀ x ∈ D, TendstoInProbability P (fun ε ω => F ε ω x) (fun ω => U ω x))
    (hnet : ∀ t : ℝ, 0 < t → ∀ e : ℝ≥0∞, 0 < e →
      ∃ K : Finset α, (∀ x ∈ K, x ∈ D) ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        P {ω | ∃ x ∈ D, ∀ y ∈ K,
          t < |F ε ω x - F ε ω y| + |U ω x - U ω y|} ≤ e) :
    ∀ t : ℝ, 0 < t → Tendsto (fun ε : ℝ => P {ω | ∃ x ∈ D,
      t < |F ε ω x - U ω x|}) (𝓝[>] 0) (𝓝 0) := by
  intro t ht
  apply ENNReal.tendsto_nhds_zero.2
  intro e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  obtain ⟨K, hKD, hK⟩ := hnet (t / 2) (by linarith) (e / 2) he2
  have hsum : Tendsto (fun ε : ℝ => ∑ x ∈ K,
      P {ω | t / 2 < |F ε ω x - U ω x|}) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_finsetSum K (fun x hx => hpoint x (hKD x hx) (t / 2) (by linarith))
  have hsum' := ENNReal.tendsto_nhds_zero.1 hsum (e / 2) he2
  filter_upwards [hK, hsum'] with ε hKε hsumε
  calc
    P {ω | ∃ x ∈ D, t < |F ε ω x - U ω x|} ≤
        P ({ω | ∃ x ∈ D, ∀ y ∈ K, t / 2 < |F ε ω x - F ε ω y| + |U ω x - U ω y|} ∪
          ⋃ y ∈ K, {ω | t / 2 < |F ε ω y - U ω y|}) := by
      apply measure_mono
      rintro ω ⟨x, hx, hbad⟩
      by_cases hnetbad : ∃ x ∈ D, ∀ y ∈ K,
          t / 2 < |F ε ω x - F ε ω y| + |U ω x - U ω y|
      · exact Or.inl hnetbad
      · have hex : ∃ y ∈ K, |F ε ω x - F ε ω y| + |U ω x - U ω y| ≤ t / 2 := by
          have hn : ¬ ∀ y ∈ K, t / 2 < |F ε ω x - F ε ω y| + |U ω x - U ω y| :=
            fun h => hnetbad ⟨x, hx, h⟩
          simpa only [not_forall, not_lt, exists_prop] using hn
        obtain ⟨y, hy, hclose⟩ := hex
        have h₁ := abs_sub_le (F ε ω x) (F ε ω y) (U ω x)
        have h₂ := abs_sub_le (F ε ω y) (U ω y) (U ω x)
        have hybad : t / 2 < |F ε ω y - U ω y| := by
          rw [abs_sub_comm (U ω y) (U ω x)] at h₂
          linarith
        exact Or.inr (mem_iUnion.2 ⟨y, mem_iUnion.2 ⟨hy, hybad⟩⟩)
    _ ≤ _ := measure_union_le _ _
    _ ≤ P {ω | ∃ x ∈ D, ∀ y ∈ K, t / 2 < |F ε ω x - F ε ω y| + |U ω x - U ω y|} +
        ∑ x ∈ K, P {ω | t / 2 < |F ε ω x - U ω x|} :=
      add_le_add le_rfl (measure_biUnion_finset_le _ _)
    _ ≤ e / 2 + e / 2 := add_le_add hKε hsumε
    _ = e := ENNReal.add_halves e

end MatedCRT
