import MatedCRT.FirstPass.Derived.JointBallStoppedPathMeasurable
import MatedCRT.FirstPass.Derived.PlanarBrownianPathContinuity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.GiryMonad

/-! # Measurability of stopped planar Brownian laws -/

set_option autoImplicit false

open MeasureTheory Metric MarkovProcess HarmonicBalls
open scoped NNReal

namespace MatedCRT.StopAtExitCmp

/-- The law of planar Brownian motion stopped on leaving an origin ball is jointly
measurable in the starting point and the radius. -/
theorem measurable_planarBrownianMotion_stopAtExit_ball :
    Measurable (fun p : ℂ × ℝ => (planarBrownianMotion p.1).map
      (fun b : ContinuousPath ℂ =>
        (⟨stopAtExit (ball (0 : ℂ) p.2) b,
          continuous_stopAtExit b.continuous⟩ : ContinuousPath ℂ))) := by
  let F : (ℂ × ℝ) × ContinuousPath ℂ → ContinuousPath ℂ := fun p =>
    ⟨stopAtExit (ball (0 : ℂ) p.1.2) (translatePath p.1.1 p.2),
      continuous_stopAtExit (translatePath p.1.1 p.2).continuous⟩
  have htrans : Continuous (fun p : (ℂ × ℝ) × ContinuousPath ℂ =>
      translatePath p.1.1 p.2) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : ((ℂ × ℝ) × ContinuousPath ℂ) × ℝ≥0 =>
      p.1.2 p.2 + p.1.1.1)
    fun_prop
  have hF : Measurable F :=
    measurable_planarBall_stopAtExit_joint.comp
      (htrans.measurable.prodMk measurable_fst.snd)
  apply Measure.measurable_measure.mpr
  intro A hA
  have hm := measurable_measure_prodMk_left (ν := planarBrownianMotion 0) (hF hA)
  convert hm using 1
  funext p
  have hstop : Measurable (fun b : ContinuousPath ℂ =>
      (⟨stopAtExit (ball (0 : ℂ) p.2) b,
        continuous_stopAtExit b.continuous⟩ : ContinuousPath ℂ)) :=
    measurable_planarBall_stopAtExit_joint.comp (measurable_id.prodMk measurable_const)
  rw [← map_translatePath_planarBrownianMotion p.1,
    Measure.map_map hstop (translatePath p.1).measurable,
    Measure.map_apply (hstop.comp (translatePath p.1).measurable) hA]
  rfl

end MatedCRT.StopAtExitCmp
