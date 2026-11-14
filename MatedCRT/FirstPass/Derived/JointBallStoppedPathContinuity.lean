import MatedCRT.FirstPass.Derived.JointBallExitAllStarts
import MatedCRT.FirstPass.Derived.StopAtExitTimeFormula
import MatedCRT.FirstPass.Derived.StopAtExitNested
import LatticeProb.Prob.ContinuousStoppedPath

/-! # Joint continuity of Brownian paths stopped at ball exit -/

set_option autoImplicit false

open MeasureTheory Metric MarkovProcess HarmonicBalls

namespace MatedCRT.StopAtExitCmp

/-- At a point of joint exit-time continuity, stopping a path at ball exit is
jointly continuous in the path and radius. -/
theorem continuousAt_planarBall_stopAtExit_joint_of_exitTime
    (b : ContinuousPath ℂ) (r : ℝ)
    (h : ContinuousAt (fun p : ContinuousPath ℂ × ℝ =>
      ContinuousPath.exitTime (ball (0 : ℂ) p.2) p.1) (b, r)) :
    ContinuousAt (fun p : ContinuousPath ℂ × ℝ =>
      (⟨stopAtExit (ball (0 : ℂ) p.2) p.1,
        continuous_stopAtExit p.1.continuous⟩ : ContinuousPath ℂ)) (b, r) := by
  have heq : (fun p : ContinuousPath ℂ × ℝ =>
      (⟨stopAtExit (ball (0 : ℂ) p.2) p.1,
        continuous_stopAtExit p.1.continuous⟩ : ContinuousPath ℂ)) =
      (fun p => LatticeProb.stoppedPath
        (ContinuousPath.exitTime (ball (0 : ℂ) p.2) p.1) p.1) := by
    funext p
    ext t
    exact stopAtExit_eq_min_exitTime _ _ _
  rw [heq]
  exact LatticeProb.continuous_stoppedPath.continuousAt.comp (h.prodMk continuousAt_fst)

/-- For each start and radius, stopping planar Brownian motion at ball exit is
almost surely jointly continuous in the path and radius. -/
theorem ae_continuousAt_planarBall_stopAtExit_joint (x : ℂ) (r : ℝ) :
    ∀ᵐ b ∂planarBrownianMotion x,
      ContinuousAt (fun p : ContinuousPath ℂ × ℝ =>
        (⟨stopAtExit (ball (0 : ℂ) p.2) p.1,
          continuous_stopAtExit p.1.continuous⟩ : ContinuousPath ℂ)) (b, r) := by
  filter_upwards [ae_continuousAt_planarBall_exitTime_joint_all x r] with b hb
  exact continuousAt_planarBall_stopAtExit_joint_of_exitTime b r hb

end MatedCRT.StopAtExitCmp
