import MatedCRT.Proofs.Field.WholePlaneKernelAffine

/-!
# The whole-plane covariance of the circle averages at the origin

For radii `a, b ∈ (0, 1]` the whole-plane covariance of the circle averages `h_a(0)` and `h_b(0)` is
`-log max(a, b)` (Duplantier-Sheffield 2011, Section 3.1; Harmonic-Balls `wholePlaneGFFCov`). The proof uses the
mean value property of `log|·|` on circles (`circleAverage_wholePlaneCov_eq`). With `a = e^{-s}`, `b = e^{-t}`
this is `min(s, t)`: the radial process `t ↦ h_{e^{-t}}(0)` of a whole-plane GFF has the covariance of a standard
Brownian motion (`radialProcess`, `Defs/QuantumCone.lean`).
-/

namespace MatedCRT.Field

open MeasureTheory Filter Set Metric HarmonicBalls

/-- The covariance of the circle averages at `0` of radii `a, b ∈ (0, 1]` is `-log max(a, b)`. -/
theorem wholePlaneGFFCov_origin_circles {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1) :
    wholePlaneGFFCov (.circle a 0) (.circle b 0) = -Real.log (max a b) := by
  have hF0 : Real.circleAverage (fun w : ℂ => Real.log (max ‖w‖ 1)) 0 b = 0 := by
    have hc : Real.circleAverage (fun w : ℂ => Real.log (max ‖w‖ 1)) 0 b
        = Real.circleAverage (fun _ : ℂ => (0 : ℝ)) 0 b := by
      refine Real.circleAverage_congr_sphere ?_
      intro w hw
      have hwb : ‖w‖ = b := by simpa [abs_of_pos hb] using hw
      simp [hwb, max_eq_right hb1]
    rw [hc, Real.circleAverage_const]
  have hinner : ∀ x ∈ Metric.sphere (0 : ℂ) |a|,
      Real.circleAverage (fun y => HarmonicBalls.wholePlaneCov x y) 0 b
        = -(Real.log b + Real.posLog (b⁻¹ * a)) := by
    intro x hx
    have hxa : ‖x‖ = a := by simpa [abs_of_pos ha] using hx
    rw [circleAverage_wholePlaneCov_eq 0 x hb, hF0, hxa, zero_sub, norm_neg, hxa, max_eq_right ha1,
      Real.log_one]
    ring
  show Real.circleAverage (fun x => Real.circleAverage (fun y => HarmonicBalls.wholePlaneCov x y) 0 b) 0 a
    = -Real.log (max a b)
  rw [Real.circleAverage_congr_sphere (f₂ := fun _ => -(Real.log b + Real.posLog (b⁻¹ * a)))
    (fun x hx => hinner x hx), Real.circleAverage_const]
  rcases le_total a b with hab | hab
  · have h1 : b⁻¹ * a ≤ 1 := by
      rw [← div_eq_inv_mul]
      exact (div_le_one hb).2 hab
    have h2 : Real.posLog (b⁻¹ * a) = 0 := by
      unfold Real.posLog
      exact max_eq_left (Real.log_nonpos (by positivity) h1)
    rw [h2, max_eq_right hab]
    ring
  · have h1 : 1 ≤ b⁻¹ * a := by
      rw [← div_eq_inv_mul]
      exact (one_le_div hb).2 hab
    have h2 : Real.posLog (b⁻¹ * a) = Real.log a - Real.log b := by
      unfold Real.posLog
      rw [max_eq_right (Real.log_nonneg h1), Real.log_mul (inv_ne_zero hb.ne') ha.ne', Real.log_inv]
      ring
    rw [h2, max_eq_left hab]
    ring

end MatedCRT.Field

