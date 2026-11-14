import MatedCRT.FirstPass.Derived.JointBallExitAllStarts
import MatedCRT.FirstPass.Derived.JointBallExitMeasurable
import MatedCRT.FirstPass.Derived.JointBallStoppedBrownianLawContinuity

/-! # Joint laws of planar Brownian paths and ball-exit clocks -/

set_option autoImplicit false

open MeasureTheory Metric MarkovProcess HarmonicBalls Filter
open scoped Topology NNReal ENNReal

namespace MatedCRT.StopAtExitCmp

/-- The path paired with its exit time from an origin ball. -/
noncomputable def planarBallPathClock (r : ℝ) (b : ContinuousPath ℂ) : ContinuousPath ℂ × ℝ≥0∞ :=
  (b, ContinuousPath.exitTime (ball (0 : ℂ) r) b)

/-- The path and its ball-exit clock are jointly Borel in path and radius. -/
theorem measurable_planarBallPathClock :
    Measurable (fun p : ContinuousPath ℂ × ℝ => planarBallPathClock p.2 p.1) :=
  measurable_fst.prodMk MatedCRT.measurable_planarBall_exitTime_joint

/-- The law of a planar Brownian path paired with its ball-exit time. -/
noncomputable def planarBrownianPathClockLaw (x : ℂ) (r : ℝ) :
    ProbabilityMeasure (ContinuousPath ℂ × ℝ≥0∞) := by
  have hf : Measurable (planarBallPathClock r) :=
    measurable_planarBallPathClock.comp (measurable_id.prodMk measurable_const)
  exact ⟨(planarBrownianMotion x).map (planarBallPathClock r),
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 inferInstance⟩

/-- The joint path and ball-exit-time law is weakly continuous in start and radius. -/
theorem continuous_planarBrownianPathClockLaw :
    Continuous (fun p : ℂ × ℝ => planarBrownianPathClockLaw p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let F : (ℂ × ℝ) → ContinuousPath ℂ → ContinuousPath ℂ × ℝ≥0∞ := fun q b =>
    planarBallPathClock q.2 (translatePath q.1 b)
  have htrans : Continuous (fun q : (ℂ × ℝ) × ContinuousPath ℂ =>
      translatePath q.1.1 q.2) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun q : ((ℂ × ℝ) × ContinuousPath ℂ) × ℝ≥0 =>
      q.1.2 q.2 + q.1.1.1)
    fun_prop
  have hmeas : ∀ q, Measurable (F q) := by
    intro q
    exact measurable_planarBallPathClock.comp
      ((translatePath q.1).measurable.prodMk measurable_const)
  have hae : ∀ᵐ b ∂planarBrownianMotion 0,
      ContinuousAt (fun q => F q b) p := by
    have h := ae_continuousAt_planarBall_exitTime_joint_all p.1 p.2
    rw [← map_translatePath_planarBrownianMotion p.1] at h
    filter_upwards [ae_of_ae_map (translatePath p.1).measurable.aemeasurable h] with b hb
    have ht : ContinuousAt (fun q : ℂ × ℝ => (translatePath q.1 b, q.2)) p :=
      (htrans.comp (continuous_id.prodMk continuous_const)).continuousAt.prodMk
        continuousAt_snd
    exact ((htrans.comp (continuous_id.prodMk continuous_const)).continuousAt).prodMk
      (ContinuousAt.comp' (f := fun q : ℂ × ℝ => (translatePath q.1 b, q.2)) hb ht)
  have hd := tendstoInDistribution_of_ae_tendsto
    (l := 𝓝 p) (μ' := planarBrownianMotion 0)
    (fun q => (hmeas q).aemeasurable) (hmeas p).aemeasurable hae
  have hlaw : ∀ q, (planarBrownianMotion 0).map (F q) =
      (planarBrownianPathClockLaw q.1 q.2 : Measure (ContinuousPath ℂ × ℝ≥0∞)) := by
    intro q
    change _ = (planarBrownianMotion q.1).map _
    have hs : Measurable (planarBallPathClock q.2) :=
      measurable_planarBallPathClock.comp (measurable_id.prodMk measurable_const)
    change (planarBrownianMotion 0).map (planarBallPathClock q.2 ∘ translatePath q.1) = _
    rw [← map_translatePath_planarBrownianMotion q.1,
      Measure.map_map hs (translatePath q.1).measurable]
  have heq : (fun q => (⟨(planarBrownianMotion 0).map (F q),
      (Measure.isProbabilityMeasure_map_iff (hmeas q).aemeasurable).2 inferInstance⟩ :
      ProbabilityMeasure (ContinuousPath ℂ × ℝ≥0∞))) =
      (fun q => planarBrownianPathClockLaw q.1 q.2) := by
    funext q
    exact Subtype.ext (hlaw q)
  have ht := hd.tendsto
  rw [heq] at ht
  have hp : (⟨(planarBrownianMotion 0).map (F p),
      (Measure.isProbabilityMeasure_map_iff (hmeas p).aemeasurable).2 inferInstance⟩ :
      ProbabilityMeasure (ContinuousPath ℂ × ℝ≥0∞)) = planarBrownianPathClockLaw p.1 p.2 :=
    Subtype.ext (hlaw p)
  rw [hp] at ht
  exact ht

end MatedCRT.StopAtExitCmp
