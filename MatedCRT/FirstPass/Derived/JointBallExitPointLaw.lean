import MatedCRT.FirstPass.Derived.EuclideanBrownianPathClockLaw
import LatticeProb.Prob.ContinuousMappingAECont

/-! # Joint continuity of Brownian ball-exit point laws -/

set_option autoImplicit false

open MeasureTheory Metric MarkovProcess HarmonicBalls Filter Topology
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

/-- The point of a path at an extended clock, totalized at infinity. -/
noncomputable def pathClockPoint (p : ContinuousPath ℂ × ℝ≥0∞) : ℂ :=
  p.1 p.2.toNNReal

/-- Evaluating a path at an extended clock is Borel. -/
theorem measurable_pathClockPoint : Measurable pathClockPoint :=
  (ContinuousEval.continuous_eval (F := ContinuousPath ℂ)).measurable.comp
    (measurable_fst.prodMk (ENNReal.measurable_toNNReal.comp measurable_snd))

/-- Evaluation is continuous at finite clocks. -/
theorem continuousAt_pathClockPoint (p : ContinuousPath ℂ × ℝ≥0∞) (hp : p.2 ≠ ⊤) :
    ContinuousAt pathClockPoint p := by
  exact (ContinuousEval.continuous_eval (F := ContinuousPath ℂ)).continuousAt.tendsto.comp
    (continuous_fst.continuousAt.tendsto.prodMk_nhds
      ((ENNReal.tendsto_toNNReal hp).comp continuous_snd.continuousAt.tendsto))

/-- The law of the point at which planar Brownian motion exits an origin ball. -/
noncomputable def planarBrownianBallExitPointLaw (x : ℂ) (r : ℝ) : ProbabilityMeasure ℂ :=
  (planarBrownianPathClockLaw x r).map pathClockPoint

/-- Brownian exit-point laws vary weakly continuously in the start and radius. -/
theorem continuous_planarBrownianBallExitPointLaw :
    Continuous (fun p : ℂ × ℝ => planarBrownianBallExitPointLaw p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hfin : ∀ᵐ q ∂(planarBrownianPathClockLaw p.1 p.2 :
      Measure (ContinuousPath ℂ × ℝ≥0∞)), q.2 ≠ ⊤ := by
    have h : ∀ᵐ b ∂planarBrownianMotion p.1,
        ContinuousPath.exitTime (ball (0 : ℂ) p.2) b ≠ ⊤ := by
      filter_upwards [HarmonicBalls.Section6.ae_planarBrownian_exitTime_bounded_lt_top p.1
        (isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) p.2))] with b hb
      exact hb.ne
    have hm : Measurable (planarBallPathClock p.2) :=
      measurable_planarBallPathClock.comp (measurable_id.prodMk measurable_const)
    change ∀ᵐ q ∂(planarBrownianMotion p.1).map (planarBallPathClock p.2), q.2 ≠ ⊤
    exact (ae_map_iff hm.aemeasurable (by measurability)).2 h
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro g
  have h := LatticeProb.tendsto_integral_of_ae_continuousAt
    continuous_planarBrownianPathClockLaw.continuousAt.tendsto
    (g.continuous.measurable.comp measurable_pathClockPoint)
    ⟨‖g‖, fun q => by simpa only [Real.norm_eq_abs, Function.comp_apply] using
      g.norm_coe_le_norm (pathClockPoint q)⟩
    (hfin.mono fun q hq => g.continuous.continuousAt.comp (continuousAt_pathClockPoint q hq))
  change Tendsto (fun q : ℂ × ℝ => ∫ y, g y ∂((planarBrownianPathClockLaw q.1 q.2 :
    Measure _).map pathClockPoint)) (𝓝 p)
    (𝓝 (∫ y, g y ∂((planarBrownianPathClockLaw p.1 p.2 : Measure _).map pathClockPoint)))
  simpa only [integral_map measurable_pathClockPoint.aemeasurable
    g.continuous.measurable.aestronglyMeasurable, Function.comp_apply] using h

/-- Evaluating the path-clock pair gives the ball-exit point. -/
theorem pathClockPoint_planarBallPathClock (r : ℝ) (b : ContinuousPath ℂ) :
    pathClockPoint (planarBallPathClock r b) = exitPoint (ball (0 : ℂ) r) b := rfl

end MatedCRT.StopAtExitCmp
