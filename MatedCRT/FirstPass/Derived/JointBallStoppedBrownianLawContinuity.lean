import MatedCRT.FirstPass.Derived.JointBallStoppedPathContinuity
import MatedCRT.FirstPass.Derived.JointBallStoppedBrownianProbability
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! # Weak continuity of stopped planar Brownian laws -/

set_option autoImplicit false

open MeasureTheory Metric MarkovProcess HarmonicBalls Filter
open scoped Topology NNReal

namespace MatedCRT.StopAtExitCmp

/-- The law of planar Brownian motion stopped on exiting an origin ball varies
weakly continuously in its initial point and the ball radius. -/
theorem continuous_planarBrownianStoppedBallLaw :
    Continuous (fun p : ℂ × ℝ => planarBrownianStoppedBallLaw p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let F : (ℂ × ℝ) → ContinuousPath ℂ → ContinuousPath ℂ := fun q b =>
    ⟨stopAtExit (ball (0 : ℂ) q.2) (translatePath q.1 b),
      continuous_stopAtExit (translatePath q.1 b).continuous⟩
  have htrans : Continuous (fun q : (ℂ × ℝ) × ContinuousPath ℂ =>
      translatePath q.1.1 q.2) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun q : ((ℂ × ℝ) × ContinuousPath ℂ) × ℝ≥0 =>
      q.1.2 q.2 + q.1.1.1)
    fun_prop
  have hmeas : ∀ q, Measurable (F q) := by
    intro q
    exact measurable_planarBall_stopAtExit_joint.comp
      ((translatePath q.1).measurable.prodMk measurable_const)
  have hae : ∀ᵐ b ∂planarBrownianMotion 0,
      ContinuousAt (fun q => F q b) p := by
    have h := ae_continuousAt_planarBall_stopAtExit_joint p.1 p.2
    rw [← map_translatePath_planarBrownianMotion p.1] at h
    filter_upwards [ae_of_ae_map (translatePath p.1).measurable.aemeasurable h] with b hb
    have ht : ContinuousAt (fun q : ℂ × ℝ => (translatePath q.1 b, q.2)) p :=
      (htrans.comp (continuous_id.prodMk continuous_const)).continuousAt.prodMk
        continuousAt_snd
    exact ContinuousAt.comp' (f := fun q : ℂ × ℝ => (translatePath q.1 b, q.2)) hb ht
  have hd := tendstoInDistribution_of_ae_tendsto
    (l := 𝓝 p) (μ' := planarBrownianMotion 0)
    (fun q => (hmeas q).aemeasurable) (hmeas p).aemeasurable hae
  have hlaw : ∀ q, (planarBrownianMotion 0).map (F q) =
      (planarBrownianStoppedBallLaw q.1 q.2 : Measure (ContinuousPath ℂ)) := by
    intro q
    change _ = (planarBrownianMotion q.1).map _
    let stop : ContinuousPath ℂ → ContinuousPath ℂ := fun b =>
      ⟨stopAtExit (ball (0 : ℂ) q.2) b, continuous_stopAtExit b.continuous⟩
    have hs : Measurable stop := measurable_planarBall_stopAtExit_joint.comp
      (measurable_id.prodMk measurable_const)
    change (planarBrownianMotion 0).map (stop ∘ translatePath q.1) =
      (planarBrownianMotion q.1).map stop
    rw [← map_translatePath_planarBrownianMotion q.1,
      Measure.map_map hs (translatePath q.1).measurable]
  have heq : (fun q => (⟨(planarBrownianMotion 0).map (F q),
      (Measure.isProbabilityMeasure_map_iff (hmeas q).aemeasurable).2 inferInstance⟩ :
      ProbabilityMeasure (ContinuousPath ℂ))) =
      (fun q => planarBrownianStoppedBallLaw q.1 q.2) := by
    funext q
    exact Subtype.ext (hlaw q)
  have ht := hd.tendsto
  rw [heq] at ht
  have hp : (⟨(planarBrownianMotion 0).map (F p),
      (Measure.isProbabilityMeasure_map_iff (hmeas p).aemeasurable).2 inferInstance⟩ :
      ProbabilityMeasure (ContinuousPath ℂ)) = planarBrownianStoppedBallLaw p.1 p.2 :=
    Subtype.ext (hlaw p)
  rw [hp] at ht
  exact ht

end MatedCRT.StopAtExitCmp
