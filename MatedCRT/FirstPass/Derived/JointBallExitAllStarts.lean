import MatedCRT.FirstPass.Derived.JointBallExitOffCircle
import MatedCRT.FirstPass.Derived.JointBallExitZero

/-! # Joint ball-exit continuity for Brownian motion -/

set_option autoImplicit false

open MeasureTheory Metric MarkovProcess HarmonicBalls

namespace MatedCRT.StopAtExitCmp

/-- For each start and radius, Brownian ball-exit time is almost surely continuous
jointly in the path and radius. -/
theorem ae_continuousAt_planarBall_exitTime_joint_all (x : ℂ) (r : ℝ) :
    ∀ᵐ b ∂planarBrownianMotion x,
      ContinuousAt (fun p : ContinuousPath ℂ × ℝ =>
        ContinuousPath.exitTime (ball (0 : ℂ) p.2) p.1) (b, r) := by
  by_cases h : r = dist x 0
  · by_cases hr : 0 < r
    · exact ae_continuousAt_planarBall_exitTime_joint_of_boundary hr h.symm
    · have hr0 : r = 0 := le_antisymm (le_of_not_gt hr) (h ▸ dist_nonneg)
      have hx : x = 0 := dist_eq_zero.mp (h.symm.trans hr0)
      subst x
      subst r
      exact ae_continuousAt_planarBall_exitTime_joint_zero
  · exact ae_continuousAt_planarBall_exitTime_joint_of_ne h

end MatedCRT.StopAtExitCmp
