import MatedCRT.FirstPass.Derived.JointBallExitExterior

/-! # Joint ball-exit continuity for Brownian starts off the circle -/

set_option autoImplicit false

open MeasureTheory Filter Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

/-- For a Brownian starting point off the radius circle, the ball exit time is
almost surely continuous jointly in the path and the radius. -/
theorem ae_continuousAt_planarBall_exitTime_joint_of_ne {x : ℂ} {r : ℝ}
    (h : r ≠ dist x 0) :
    ∀ᵐ b ∂planarBrownianMotion x,
      ContinuousAt (fun p : ContinuousPath ℂ × ℝ =>
        ContinuousPath.exitTime (ball (0 : ℂ) p.2) p.1) (b, r) := by
  rcases lt_or_gt_of_ne h with hr | hr
  · filter_upwards [ae_planarBrownianMotion_eval_zero x] with b hb
    apply continuousAt_planarBall_exitTime_joint_of_initial_exterior
    simpa only [hb] using hr
  · exact ae_continuousAt_planarBall_exitTime_joint hr

end MatedCRT.StopAtExitCmp
