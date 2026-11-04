import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.NearPoleComparison

/-! Passing a one-sided probability bound to an absolute-value bound. -/

namespace MatedCRT

open Set Filter Topology MeasureTheory _root_.HarmonicBalls
open scoped ENNReal

/-- If random variables are nonnegative on events tending to probability one,
a one-sided tail bound also controls their absolute-value tails. -/
theorem eventually_abs_tail_le_of_nonneg
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (E : ℝ → Set Ω)
    (F : ℝ → Ω → ℝ)
    (hnonneg : ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂P, ω ∈ E ε → 0 ≤ F ε ω)
    (hE : ProbTendsToOne P E) {t : ℝ} {b e : ℝ≥0∞} (he : 0 < e)
    (htail : ∀ᶠ ε in 𝓝[>] (0 : ℝ), P {ω | t < F ε ω} ≤ b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), P {ω | t < |F ε ω|} ≤ b + e := by
  have hsmall := ENNReal.tendsto_nhds_zero.1 hE e he
  filter_upwards [hsmall, htail, self_mem_nhdsWithin] with ε hsmall htail hε
  calc
    P {ω | t < |F ε ω|} ≤ P ({ω | t < F ε ω} ∪ (E ε)ᶜ) := by
      apply measure_mono_ae
      filter_upwards [hnonneg ε hε] with ω hω
      intro h
      by_cases hmem : ω ∈ E ε
      · left
        simpa [abs_of_nonneg (hω hmem)] using h
      · exact Or.inr hmem
    _ ≤ P {ω | t < F ε ω} + P (E ε)ᶜ := measure_union_le _ _
    _ ≤ b + e := add_le_add htail hsmall

end MatedCRT
