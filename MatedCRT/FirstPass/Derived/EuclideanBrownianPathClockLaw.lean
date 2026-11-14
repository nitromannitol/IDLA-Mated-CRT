import MatedCRT.FirstPass.Derived.JointBallBrownianPathClockLaw
import MatedCRT.FirstPass.Derived.EuclideanBallExitMeasurable
import MatedCRT.FirstPass.Derived.JointBallExitPoint

/-! # Brownian path and ball-exit clock in Euclidean coordinates -/

set_option autoImplicit false

open MeasureTheory Metric MarkovProcess HarmonicBalls Filter
open MatedCRT.TargetLawTemplateEvent
open scoped Topology ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

/-- Read a complex path-clock pair in orthonormal Euclidean coordinates. -/
noncomputable def pathClockToEuclidean (p : ContinuousPath ℂ × ℝ≥0∞) :
    ContinuousPath (EuclideanSpace ℝ (Fin 2)) × ℝ≥0∞ :=
  (complexPathToEuc p.1, p.2)

/-- The coordinate map on path-clock pairs is continuous. -/
theorem continuous_pathClockToEuclidean : Continuous pathClockToEuclidean :=
  (continuous_complexPathToEuc.comp continuous_fst).prodMk continuous_snd

/-- The transported clock is the exit time of the Euclidean path from the same ball. -/
theorem pathClockToEuclidean_planarBallPathClock (r : ℝ) (b : ContinuousPath ℂ) :
    pathClockToEuclidean (planarBallPathClock r b) =
      (complexPathToEuc b, ContinuousPath.exitTime
        (ball (0 : EuclideanSpace ℝ (Fin 2)) r) (complexPathToEuc b)) := by
  simp only [pathClockToEuclidean, planarBallPathClock, exitTime_ball_complexPathToEuc]

/-- The Euclidean coordinate law of the Brownian path and its ball-exit clock. -/
noncomputable def euclideanBrownianPathClockLaw (x : ℂ) (r : ℝ) :
    ProbabilityMeasure (ContinuousPath (EuclideanSpace ℝ (Fin 2)) × ℝ≥0∞) :=
  (planarBrownianPathClockLaw x r).map pathClockToEuclidean

/-- The Euclidean path-clock law is weakly continuous in start and radius. -/
theorem continuous_euclideanBrownianPathClockLaw :
    Continuous (fun p : ℂ × ℝ => euclideanBrownianPathClockLaw p.1 p.2) :=
  (ProbabilityMeasure.continuous_map continuous_pathClockToEuclidean).comp
    continuous_planarBrownianPathClockLaw

/-- The clock in the Euclidean path-clock law is almost surely finite. -/
theorem ae_euclideanBrownianPathClockLaw_clock_ne_top (x : ℂ) (r : ℝ) :
    ∀ᵐ p ∂(euclideanBrownianPathClockLaw x r :
      Measure (ContinuousPath (EuclideanSpace ℝ (Fin 2)) × ℝ≥0∞)), p.2 ≠ ⊤ := by
  have h : ∀ᵐ b ∂planarBrownianMotion x,
      ContinuousPath.exitTime (ball (0 : ℂ) r) b ≠ ⊤ := by
    filter_upwards [HarmonicBalls.Section6.ae_planarBrownian_exitTime_bounded_lt_top x
      (isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) r))] with b hb
    exact hb.ne
  have hm : Measurable (planarBallPathClock r) :=
    measurable_planarBallPathClock.comp (measurable_id.prodMk measurable_const)
  change ∀ᵐ p ∂((planarBrownianMotion x).map (planarBallPathClock r) |>.map
    pathClockToEuclidean), p.2 ≠ ⊤
  rw [Measure.map_map continuous_pathClockToEuclidean.measurable hm]
  apply (ae_map_iff (continuous_pathClockToEuclidean.measurable.comp hm).aemeasurable
    (by measurability)).2
  exact h

end MatedCRT.StopAtExitCmp
