import MatedCRT.FirstPass.Derived.BrownianExitKernelContinuity
import HarmonicBalls.Proofs.Sec6.AvoidanceDiscRestart

/-! # Normalized centered planar Brownian disc exit law -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric HarmonicBalls HarmonicBalls.Section6

namespace MatedCRT

/-- After normalization, Brownian motion started at the center of a disc exits
with the normalized angular distribution on the unit circle. -/
theorem planarBrownianExitProbability_ball_center_normalize
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ((planarBrownianExitProbability (ball c r) isOpen_ball c : ProbabilityMeasure ℂ) :
      Measure ℂ).map (fun w => r⁻¹ • (w - c)) = normalizedCircleMeasure 0 1 := by
  change ((planarBrownianMotion c).map
      (fun ω => ω ((MarkovProcess.ContinuousPath.exitTime (ball c r) ω).toNNReal))).map
      (fun w => r⁻¹ • (w - c)) = normalizedCircleMeasure 0 1
  rw [planarBrownian_disc_exit_distribution hr]
  unfold normalizedCircleMeasure
  rw [Measure.map_map (by fun_prop) (continuous_circleMap c r).measurable]
  congr 1
  funext θ
  simp only [Function.comp_apply, circleMap, add_sub_cancel_left, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_one, one_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne'), one_mul, zero_add]

end MatedCRT
end
