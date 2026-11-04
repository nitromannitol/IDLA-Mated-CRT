import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.CenteredNormalizedPotential

/-! The signed source measures for a nonnegative buffered bump. -/

namespace MatedCRT

open MeasureTheory
open scoped ENNReal

/-- The positive part of the negative bump source vanishes. -/
theorem negativeBump_positive_source_eq_zero
    (μ : Measure ℂ) {c : ℝ} (hc : 0 ≤ c) (φ : ℂ → ℝ) (hφ : ∀ x, 0 ≤ φ x) :
    μ.withDensity (fun x => ENNReal.ofReal (c * -φ x)) = 0 := by
  have h : (fun x => ENNReal.ofReal (c * -φ x)) = 0 := by
    funext x
    exact ENNReal.ofReal_eq_zero.mpr (mul_nonpos_of_nonneg_of_nonpos hc (neg_nonpos.mpr (hφ x)))
  rw [h]
  simp

/-- The negative part of the negative bump source is its density measure. -/
theorem negativeBump_negative_source_eq_smul
    (μ : Measure ℂ) {c : ℝ} (hc : 0 ≤ c) (φ : ℂ → ℝ) (hφm : Measurable φ) :
    μ.withDensity (fun x => ENNReal.ofReal (-(c * -φ x))) =
      ENNReal.ofReal c • μ.withDensity (fun x => ENNReal.ofReal (φ x)) := by
  have h : (fun x => ENNReal.ofReal (-(c * -φ x))) =
      ENNReal.ofReal c • (fun x => ENNReal.ofReal (φ x)) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, mul_neg, neg_neg]
    exact ENNReal.ofReal_mul hc
  rw [h]
  exact withDensity_smul (μ := μ) (ENNReal.ofReal c)
    (f := fun x => ENNReal.ofReal (φ x)) (ENNReal.measurable_ofReal.comp hφm)

end MatedCRT
