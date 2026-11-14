import MatedCRT.FirstPass.Derived.JointBallStoppedBrownianLaw
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! # Probability laws of stopped planar Brownian motion -/

set_option autoImplicit false

open MeasureTheory Metric MarkovProcess HarmonicBalls
open scoped NNReal

namespace MatedCRT.StopAtExitCmp

/-- The law of planar Brownian motion stopped at the exit of an origin ball. -/
noncomputable def planarBrownianStoppedBallLaw (z : ℂ) (r : ℝ) :
    ProbabilityMeasure (ContinuousPath ℂ) := by
  let f : ContinuousPath ℂ → ContinuousPath ℂ := fun b =>
    ⟨stopAtExit (ball (0 : ℂ) r) b, continuous_stopAtExit b.continuous⟩
  have hf : Measurable f :=
    measurable_planarBall_stopAtExit_joint.comp (measurable_id.prodMk measurable_const)
  exact ⟨(planarBrownianMotion z).map f,
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 inferInstance⟩

/-- Stopped planar Brownian probability laws are jointly measurable in the start
and the radius. -/
theorem measurable_planarBrownianStoppedBallLaw :
    Measurable (fun p : ℂ × ℝ => planarBrownianStoppedBallLaw p.1 p.2) := by
  exact measurable_planarBrownianMotion_stopAtExit_ball.subtype_mk

end MatedCRT.StopAtExitCmp
