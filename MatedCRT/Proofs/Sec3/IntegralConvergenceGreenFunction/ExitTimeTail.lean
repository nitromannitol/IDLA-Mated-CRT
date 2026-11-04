import MatedCRT.Steps.Sec3.IntegralConvergenceGreenFunction
import MatedCRT.Proofs.IDLA.Measurable

/-!
# Second-moment control of exit-time tails

The tail estimate used in the truncation argument for Lemma 3.4 follows from
an upper bound on the second moment, rather than from a first-moment bound.
-/

namespace MatedCRT

open MeasureTheory Set
open scoped ENNReal NNReal

/-- A second moment controls the first moment on a tail, for a measurable random variable. -/
theorem lintegral_tail_mul_le_secondMoment {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (X : α → ℝ≥0∞) (hX : Measurable X) (T : ℝ≥0∞) (hT : T ≠ ⊤) :
    T * (∫⁻ x in {x | T ≤ X x}, X x ∂μ) ≤ ∫⁻ x, (X x) ^ 2 ∂μ := by
  rw [← lintegral_const_mul' T X hT]
  calc
    (∫⁻ x in {x | T ≤ X x}, T * X x ∂μ) ≤
        ∫⁻ x in {x | T ≤ X x}, (X x) ^ 2 ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem₀ (measurableSet_le measurable_const hX).nullMeasurableSet] with x hx
      rw [pow_two]
      gcongr
    _ ≤ ∫⁻ x, (X x) ^ 2 ∂μ := setLIntegral_le_lintegral _ _

/-- The normalized walk exit-time tail is controlled by its second exit-time
moment. The scale is a nonnegative finite number, typically `mε⁻¹`. -/
theorem scaled_exitTime_tail_le_secondMoment (m : ℤ → ℤ → ℕ) (A : Set ℤ)
    (a : ℤ) (c : ℝ≥0) (T : ℝ≥0∞) (hT : T ≠ ⊤) :
    T * (∫⁻ x in {x | T ≤ (c : ℝ≥0∞) * (vExitTime A x : ℝ≥0∞)},
      (c : ℝ≥0∞) * (vExitTime A x : ℝ≥0∞) ∂srwLaw m a) ≤
      (c : ℝ≥0∞) ^ 2 * exitTimeMoment m A a 2 := by
  have hmeas : Measurable (fun x : ℕ → ℤ =>
      (c : ℝ≥0∞) * (vExitTime A x : ℝ≥0∞)) := by
    exact measurable_const.mul ((measurable_of_countable
      (fun n : ℕ∞ => (n : ℝ≥0∞))).comp (measurable_vExitTime A))
  have h := lintegral_tail_mul_le_secondMoment (srwLaw m a)
    (fun x => (c : ℝ≥0∞) * (vExitTime A x : ℝ≥0∞)) hmeas T hT
  calc
    _ ≤ ∫⁻ x, ((c : ℝ≥0∞) * (vExitTime A x : ℝ≥0∞)) ^ 2 ∂srwLaw m a := h
    _ = (c : ℝ≥0∞) ^ 2 * exitTimeMoment m A a 2 := by
      simp only [mul_pow, exitTimeMoment]
      exact lintegral_const_mul' _ _ (by finiteness)

end MatedCRT
