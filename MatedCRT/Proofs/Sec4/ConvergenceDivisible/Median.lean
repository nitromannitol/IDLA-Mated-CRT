import MatedCRT.Steps.Sec4.ConvergenceDivisible

/-! A lower bound for the lower median used to normalize Liouville Brownian motion. -/

namespace MatedCRT

open MeasureTheory
open scoped ENNReal

/-- A lower median is positive when the distribution function is below one half near
zero and reaches one half at a finite time. -/
theorem medianOf_pos_of_cdf_bounds {cdf : ℝ → ℝ≥0∞} {δ : ℝ} (hδ : 0 < δ)
    (hsmall : ∀ x, 0 ≤ x → x < δ → cdf x < 1 / 2)
    (hfinite : ∃ x, 0 ≤ x ∧ (1 / 2 : ℝ≥0∞) ≤ cdf x) :
    0 < medianOf cdf := by
  unfold medianOf
  apply lt_of_lt_of_le hδ
  apply le_csInf hfinite
  rintro x ⟨hx, hhalf⟩
  by_contra h
  exact (not_le_of_gt (hsmall x hx (lt_of_not_ge h))) hhalf

/-- Positivity of the scaling constant follows from the two distributional properties
of the annealed Liouville Brownian exit time. -/
theorem scalingConstantPositive_of_exit_cdf_bounds
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (h : 0 < S.m₀) : 0 < S.c₀ / 6 := by
  simp only [MatedCRTEnv.c₀]
  positivity

end MatedCRT
