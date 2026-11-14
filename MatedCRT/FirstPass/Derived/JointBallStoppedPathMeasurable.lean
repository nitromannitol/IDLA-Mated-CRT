import MatedCRT.FirstPass.Derived.JointBallExitMeasurable
import MatedCRT.FirstPass.Derived.StopAtExitNested
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-! # Joint measurability of paths stopped at ball exit -/

set_option autoImplicit false

open MeasureTheory Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT

/-- Stopping a continuous path at its exit from an origin ball is jointly Borel in
the path and the radius, including infinite exit times. -/
theorem measurable_planarBall_stopAtExit_joint :
    Measurable (fun p : ContinuousPath ℂ × ℝ =>
      (⟨stopAtExit (ball (0 : ℂ) p.2) p.1,
        StopAtExitCmp.continuous_stopAtExit p.1.continuous⟩ : ContinuousPath ℂ)) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  have hτ : Measurable (fun p : ContinuousPath ℂ × ℝ =>
      pathExitTime (ball (0 : ℂ) p.2) p.1) :=
    measurable_planarBall_exitTime_joint
  have hT : Measurable (fun p : ContinuousPath ℂ × ℝ =>
      if pathExitTime (ball (0 : ℂ) p.2) p.1 = ⊤ then t
      else min t (pathExitTime (ball (0 : ℂ) p.2) p.1).toNNReal) :=
    Measurable.ite (hτ (measurableSet_singleton ⊤)) measurable_const
      (measurable_const.min (ENNReal.measurable_toNNReal.comp hτ))
  exact (ContinuousEval.continuous_eval (F := ContinuousPath ℂ)).measurable.comp
    (measurable_fst.prodMk hT)

end MatedCRT
