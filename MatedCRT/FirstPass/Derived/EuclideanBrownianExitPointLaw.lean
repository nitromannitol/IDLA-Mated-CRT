import MatedCRT.FirstPass.Derived.JointBallExitPointLaw

/-! # Brownian ball-exit points in Euclidean coordinates -/

set_option autoImplicit false

open MeasureTheory Metric MarkovProcess HarmonicBalls
open MatedCRT.TargetLawTemplateEvent
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

/-- Evaluate a Euclidean path at an extended clock, totalized at infinity. -/
noncomputable def euclideanPathClockPoint
    (p : ContinuousPath (EuclideanSpace ℝ (Fin 2)) × ℝ≥0∞) :
    EuclideanSpace ℝ (Fin 2) := p.1 p.2.toNNReal

/-- Euclidean path-clock evaluation is Borel. -/
theorem measurable_euclideanPathClockPoint : Measurable euclideanPathClockPoint :=
  (ContinuousEval.continuous_eval
    (F := ContinuousPath (EuclideanSpace ℝ (Fin 2)))).measurable.comp
    (measurable_fst.prodMk (ENNReal.measurable_toNNReal.comp measurable_snd))

/-- Path-clock evaluation commutes with the planar coordinate isometry. -/
theorem euclideanPathClockPoint_pathClockToEuclidean
    (p : ContinuousPath ℂ × ℝ≥0∞) :
    euclideanPathClockPoint (pathClockToEuclidean p) =
      Complex.orthonormalBasisOneI.repr (pathClockPoint p) := rfl

/-- The law of the planar Brownian ball-exit point in Euclidean coordinates. -/
noncomputable def euclideanBrownianBallExitPointLaw (x : ℂ) (r : ℝ) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)) :=
  (euclideanBrownianPathClockLaw x r).map euclideanPathClockPoint

/-- The Euclidean exit-point law is the coordinate image of the complex law. -/
theorem euclideanBrownianBallExitPointLaw_eq_map (x : ℂ) (r : ℝ) :
    euclideanBrownianBallExitPointLaw x r =
      (planarBrownianBallExitPointLaw x r).map Complex.orthonormalBasisOneI.repr := by
  apply Subtype.ext
  change ((planarBrownianPathClockLaw x r : Measure _).map pathClockToEuclidean).map
    euclideanPathClockPoint =
    ((planarBrownianPathClockLaw x r : Measure _).map pathClockPoint).map
      Complex.orthonormalBasisOneI.repr
  rw [Measure.map_map measurable_euclideanPathClockPoint
    continuous_pathClockToEuclidean.measurable,
    Measure.map_map Complex.orthonormalBasisOneI.repr.continuous.measurable
      measurable_pathClockPoint]
  rfl

/-- The Euclidean Brownian exit-point law is weakly continuous in start and radius. -/
theorem continuous_euclideanBrownianBallExitPointLaw :
    Continuous (fun p : ℂ × ℝ => euclideanBrownianBallExitPointLaw p.1 p.2) := by
  simp only [euclideanBrownianBallExitPointLaw_eq_map]
  exact (ProbabilityMeasure.continuous_map Complex.orthonormalBasisOneI.repr.continuous).comp
    continuous_planarBrownianBallExitPointLaw

/-- The Euclidean path-clock point agrees with the paper's complex exit point. -/
theorem euclideanPathClockPoint_planarBallPathClock (r : ℝ) (b : ContinuousPath ℂ) :
    euclideanPathClockPoint (pathClockToEuclidean (planarBallPathClock r b)) =
      Complex.orthonormalBasisOneI.repr (exitPoint (ball (0 : ℂ) r) b) := rfl

end MatedCRT.StopAtExitCmp
