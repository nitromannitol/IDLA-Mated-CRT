import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.ModulusConvergence

/-! Separate moduli for the discrete and continuum functions. -/

namespace MatedCRT

open Set Filter Topology MeasureTheory Metric _root_.HarmonicBalls
open scoped ENNReal

/-- Pointwise convergence is uniform in probability on a compact set when the
discrete functions and their limit each have a probabilistic modulus. -/
theorem uniformInProbability_of_separate_moduli
    {Ω α : Type*} [MeasurableSpace Ω] [PseudoMetricSpace α]
    (P : Measure Ω) (D : Set α) (hD : IsCompact D)
    (F : ℝ → Ω → α → ℝ) (U : Ω → α → ℝ)
    (hpoint : ∀ x ∈ D, TendstoInProbability P (fun ε ω => F ε ω x) (fun ω => U ω x))
    (hF : ∀ t : ℝ, 0 < t → ∀ e : ℝ≥0∞, 0 < e → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), P {ω | ∃ x ∈ D, ∃ y ∈ D, dist x y < δ ∧
        t < |F ε ω x - F ε ω y|} ≤ e)
    (hU : ∀ t : ℝ, 0 < t → ∀ e : ℝ≥0∞, 0 < e → ∃ δ : ℝ, 0 < δ ∧
      P {ω | ∃ x ∈ D, ∃ y ∈ D, dist x y < δ ∧ t < |U ω x - U ω y|} ≤ e) :
    ∀ t : ℝ, 0 < t → Tendsto (fun ε : ℝ => P {ω | ∃ x ∈ D,
      t < |F ε ω x - U ω x|}) (𝓝[>] 0) (𝓝 0) := by
  apply uniformInProbability_of_asymptotic_modulus P D hD F U hpoint
  intro t ht e he
  have ht2 : 0 < t / 2 := by linarith
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  obtain ⟨δF, hδF, hFδ⟩ := hF (t / 2) ht2 (e / 2) he2
  obtain ⟨δU, hδU, hUδ⟩ := hU (t / 2) ht2 (e / 2) he2
  refine ⟨min δF δU, lt_min hδF hδU, ?_⟩
  filter_upwards [hFδ] with ε hε
  calc
    P {ω | ∃ x ∈ D, ∃ y ∈ D, dist x y < min δF δU ∧
        t < |F ε ω x - F ε ω y| + |U ω x - U ω y|} ≤
      P ({ω | ∃ x ∈ D, ∃ y ∈ D, dist x y < δF ∧ t / 2 < |F ε ω x - F ε ω y|} ∪
         {ω | ∃ x ∈ D, ∃ y ∈ D, dist x y < δU ∧ t / 2 < |U ω x - U ω y|}) := by
      apply measure_mono
      rintro ω ⟨x, hx, y, hy, hdist, hbad⟩
      by_cases h : t / 2 < |F ε ω x - F ε ω y|
      · exact Or.inl ⟨x, hx, y, hy, hdist.trans_le (min_le_left _ _), h⟩
      · exact Or.inr ⟨x, hx, y, hy, hdist.trans_le (min_le_right _ _), by linarith⟩
    _ ≤ _ := measure_union_le _ _
    _ ≤ e / 2 + e / 2 := add_le_add hε hUδ
    _ = e := ENNReal.add_halves e

end MatedCRT
