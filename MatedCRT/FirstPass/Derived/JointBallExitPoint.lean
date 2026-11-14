import MatedCRT.FirstPass.Derived.JointBallExitAllStarts
import MatedCRT.FirstPass.Derived.ExitPointLocalUniform

/-! # Joint ball-exit point measurability and continuity -/

set_option autoImplicit false

open MeasureTheory Metric MarkovProcess HarmonicBalls Filter Topology
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

/-- The ball-exit point is jointly Borel in the path and radius. -/
theorem measurable_planarBall_exitPoint_joint :
    Measurable (fun p : ContinuousPath ℂ × ℝ =>
      exitPoint (ball (0 : ℂ) p.2) p.1) := by
  have hτ : Measurable (fun p : ContinuousPath ℂ × ℝ =>
      (ContinuousPath.exitTime (ball (0 : ℂ) p.2) p.1).toNNReal) :=
    ENNReal.measurable_toNNReal.comp MatedCRT.measurable_planarBall_exitTime_joint
  exact (ContinuousEval.continuous_eval (F := ContinuousPath ℂ)).measurable.comp
    (measurable_fst.prodMk hτ)

/-- At a finite, jointly continuous ball-exit clock, the exit point is jointly continuous. -/
theorem continuousAt_planarBall_exitPoint_joint {b : ContinuousPath ℂ} {r : ℝ}
    (hfin : ContinuousPath.exitTime (ball (0 : ℂ) r) b ≠ ⊤)
    (hτ : ContinuousAt (fun p : ContinuousPath ℂ × ℝ =>
      ContinuousPath.exitTime (ball (0 : ℂ) p.2) p.1) (b, r)) :
    ContinuousAt (fun p : ContinuousPath ℂ × ℝ =>
      exitPoint (ball (0 : ℂ) p.2) p.1) (b, r) := by
  have hT : Tendsto (fun p : ContinuousPath ℂ × ℝ =>
      (ContinuousPath.exitTime (ball (0 : ℂ) p.2) p.1).toNNReal) (𝓝 (b, r))
      (𝓝 (ContinuousPath.exitTime (ball (0 : ℂ) r) b).toNNReal) :=
    (ENNReal.tendsto_toNNReal hfin).comp hτ
  exact (ContinuousEval.continuous_eval (F := ContinuousPath ℂ)).continuousAt.tendsto.comp
    (continuous_fst.continuousAt.tendsto.prodMk_nhds hT)

/-- For each fixed start and radius, the ball-exit point is jointly continuous almost surely. -/
theorem ae_continuousAt_planarBall_exitPoint_joint (x : ℂ) (r : ℝ) :
    ∀ᵐ b ∂planarBrownianMotion x,
      ContinuousAt (fun p : ContinuousPath ℂ × ℝ =>
        exitPoint (ball (0 : ℂ) p.2) p.1) (b, r) := by
  filter_upwards [ae_continuousAt_planarBall_exitTime_joint_all x r,
    HarmonicBalls.Section6.ae_planarBrownian_exitTime_bounded_lt_top x
      (isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) r))] with b hτ hfin
  exact continuousAt_planarBall_exitPoint_joint hfin.ne hτ

end MatedCRT.StopAtExitCmp
