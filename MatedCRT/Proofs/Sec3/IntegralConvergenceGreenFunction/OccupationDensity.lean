import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.PathOccupationEnergy
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ApproxClockOccupation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Weighted path occupation and regularized clocks -/

namespace MatedCRT

open MeasureTheory Set HarmonicBalls MarkovProcess
open scoped NNReal

/-- Integrating against a density-weighted path occupation measure gives the
weighted time integral along the path. -/
theorem pathOccupationMeasure_withDensity_integral
    (b : ContinuousPath ℂ) (T : ℝ≥0) (w f : ℂ → ℝ)
    (hw : Continuous w) (hw0 : ∀ z, 0 ≤ w z) (hf : Continuous f) :
    (∫ z, f z ∂((pathOccupationMeasure (fun t => b t.toNNReal) T).withDensity
      (fun z => ENNReal.ofReal (w z)))) =
      ∫ t in (0 : ℝ)..(T : ℝ), w (b t.toNNReal) * f (b t.toNNReal) := by
  rw [integral_withDensity_eq_integral_toReal_smul hw.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (hw0 _), smul_eq_mul]
  rw [pathOccupationMeasure, integral_map_of_stronglyMeasurable
    (show Measurable (fun t : ℝ => b t.toNNReal) from
      b.continuous.measurable.comp measurable_real_toNNReal)
    (show StronglyMeasurable (fun z => w z * f z) from (hw.mul hf).stronglyMeasurable)]
  rw [intervalIntegral.integral_of_le T.coe_nonneg, integral_Icc_eq_integral_Ioc]

/-- The density-weighted occupation measure for a circle-average clock has
the same test-function integral as its time-changed path up to clock time. -/
theorem lqgClockApprox_weighted_occupation
    (γ ε : ℝ) (hε : ℝ → ℂ → ℝ) (b : ContinuousPath ℂ)
    (hεpos : 0 < ε) (hfield : Continuous (hε ε))
    (T : ℝ≥0) (f : ℂ → ℝ) (hf : Continuous f) :
    (∫ z, f z ∂((pathOccupationMeasure (fun t => b t.toNNReal) T).withDensity
      (fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε z))))) =
      ∫ s in (0 : ℝ)..(lqgClockApprox γ hε ε b T),
        f (b (clockInverse (lqgClockApprox γ hε ε b) s.toNNReal)) := by
  rw [pathOccupationMeasure_withDensity_integral b T _ f
    (by fun_prop) (fun z => (mul_pos (Real.rpow_pos_of_pos hεpos _)
      (Real.exp_pos _)).le) hf]
  simpa only [mul_comm] using
    lqgClockApprox_occupation_substitution_local γ ε hε b hεpos hfield T f hf

end MatedCRT
