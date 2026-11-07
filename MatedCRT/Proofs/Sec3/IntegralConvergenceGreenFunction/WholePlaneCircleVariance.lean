import HarmonicBalls.Proofs.Sec2.CircleAverageTail

/-! # Interior circle-average variance of the whole-plane GFF -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Metric Set HarmonicBalls

/-- The whole-plane covariance averaged twice over a circle contained in the
unit disk is the logarithm of the inverse radius. -/
theorem wholePlaneGFFCov_circle_inside_unit {r : ℝ} (hr : 0 < r) (z : ℂ)
    (hz : ‖z‖ + r ≤ 1) :
    wholePlaneGFFCov (.circle r z) (.circle r z) = Real.log r⁻¹ := by
  change Real.circleAverage (fun x => Real.circleAverage (fun y => wholePlaneCov x y) z r) z r = _
  rw [Real.circleAverage_congr_sphere (f₂ := fun _ => -Real.log r), Real.circleAverage_const,
    Real.log_inv]
  intro x hx
  have hx' : dist x z = r := by simpa [dist_eq_norm, abs_of_pos hr] using hx
  have hxn : ‖x‖ ≤ 1 := by
    have htri : ‖x‖ ≤ ‖x - z‖ + ‖z‖ := by
      simpa using norm_add_le (x - z) z
    rw [← dist_eq_norm, hx'] at htri
    linarith
  have hi : Real.circleAverage (fun y => wholePlaneCov x y) z r =
      Real.circleAverage (fun y => -Real.log ‖y - x‖) z r := by
    apply Real.circleAverage_congr_sphere
    intro y hy
    have hy' : dist y z = r := by simpa [dist_eq_norm, abs_of_pos hr] using hy
    have hyn : ‖y‖ ≤ 1 := by
      have htri : ‖y‖ ≤ ‖y - z‖ + ‖z‖ := by
        simpa using norm_add_le (y - z) z
      rw [← dist_eq_norm, hy'] at htri
      linarith
    dsimp only
    rw [wholePlaneCov_eq_neg_log hxn hyn, norm_sub_rev]
  dsimp only
  rw [hi]
  have hnorm : ‖z - x‖ = r := by simpa [dist_eq_norm, norm_sub_rev] using hx'
  have havg := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (c := z) (a := x) hr.ne'
  rw [hnorm, inv_mul_cancel₀ hr.ne', Real.posLog_one, add_zero] at havg
  rw [Real.circleAverage_def] at havg ⊢
  rw [intervalIntegral.integral_neg, smul_neg, havg]

/-- On an interior circle, the centered whole-plane GFF average has second
moment `log (1 / r)`. -/
theorem IsWholePlaneGFF.circle_secondMoment_inside_unit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (z : ℂ)
    (hz : ‖z‖ + r ≤ 1) :
    (∫ ω, (hcirc ω r z) ^ 2 ∂P) = Real.log r⁻¹ := by
  have hG := h.hasGaussianLaw_circle hr z
  have hmean : (∫ ω, hcirc ω r z ∂P) = 0 := h.integral_eq_zero (.circle r z) hr
  have hcov := h.covariance_eq (.circle r z) (.circle r z) hr hr
  change cov[fun ω => hcirc ω r z, fun ω => hcirc ω r z; P] = _ at hcov
  rw [wholePlaneGFFCov_circle_inside_unit hr z hz] at hcov
  rw [covariance_self hG.aemeasurable, variance_eq_integral hG.aemeasurable, hmean] at hcov
  simpa using hcov

end MatedCRT
