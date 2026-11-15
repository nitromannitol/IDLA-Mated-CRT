import MatedCRT.FirstPass.Derived.NormalizedPlanarBrownianExitFrontier

/-! # Normalized planar Brownian disc exit law -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric HarmonicBalls

namespace MatedCRT

/-- A Brownian exit position from a disc, normalized about its center and by
its radius, lies on the unit circle almost surely. -/
theorem planarBrownianExitProbability_ball_normalize_ae_mem_sphere
    (c z : ℂ) {r : ℝ} (hr : 0 < r) (hz : z ∈ ball c r) :
    ∀ᵐ w ∂(((planarBrownianExitProbability (ball c r) isOpen_ball z :
      ProbabilityMeasure ℂ) : Measure ℂ).map (fun w => r⁻¹ • (w - c))),
      w ∈ sphere (0 : ℂ) 1 := by
  have hset : (fun w : ℂ => c + r • w) ⁻¹' ball c r = ball (0 : ℂ) 1 := by
    ext w
    simp only [mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left,
      sub_zero, norm_smul, Real.norm_of_nonneg hr.le]
    simpa only [mul_one] using (mul_lt_mul_iff_right₀ hr : r * ‖w‖ < r * 1 ↔ ‖w‖ < 1)
  have h := planarBrownianExitProbability_normalize_ae_mem_frontier
    (ball c r) isOpen_ball isBounded_ball c z hz hr
  simpa only [hset, frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using h

end MatedCRT
end
