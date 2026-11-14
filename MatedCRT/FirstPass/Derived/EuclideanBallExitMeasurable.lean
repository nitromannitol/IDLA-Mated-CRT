import MatedCRT.FirstPass.Derived.JointBallExitMeasurable
import MatedCRT.FirstPass.Derived.TargetLawTemplateEvent

/-! # Ball exit times in planar coordinates -/

set_option autoImplicit false

open MeasureTheory Set Metric MarkovProcess
open MatedCRT.TargetLawTemplateEvent MatedCRT.TemplateEventCompactOpen
open scoped ENNReal NNReal

namespace MatedCRT

/-- Reading a complex path in orthonormal planar coordinates preserves its ball exit time. -/
theorem exitTime_ball_complexPathToEuc (b : ContinuousPath ℂ) (r : ℝ) :
    ContinuousPath.exitTime (ball (0 : EuclideanSpace ℝ (Fin 2)) r) (complexPathToEuc b) =
      ContinuousPath.exitTime (ball (0 : ℂ) r) b := by
  unfold ContinuousPath.exitTime
  congr 1
  ext s
  simp only [Set.mem_ofPred_eq, complexPathToEuc_apply, Metric.mem_ball]
  simp only [← map_zero Complex.orthonormalBasisOneI.repr,
    Complex.orthonormalBasisOneI.repr.dist_map]

/-- Reading a Euclidean path as a complex path preserves its ball exit time. -/
theorem exitTime_ball_eucPathToComplex
    (b : ContinuousPath (EuclideanSpace ℝ (Fin 2))) (r : ℝ) :
    ContinuousPath.exitTime (ball (0 : ℂ) r) (eucPathToComplex b) =
      ContinuousPath.exitTime (ball (0 : EuclideanSpace ℝ (Fin 2)) r) b := by
  unfold ContinuousPath.exitTime
  congr 1
  ext s
  simp only [Set.mem_ofPred_eq, eucPathToComplex_apply, Metric.mem_ball]
  simp only [← map_zero Complex.orthonormalBasisOneI.repr.symm,
    Complex.orthonormalBasisOneI.repr.symm.dist_map]

/-- The Euclidean ball exit time is jointly Borel in the path and radius. -/
theorem measurable_euclideanBall_exitTime_joint :
    Measurable (fun p : ContinuousPath (EuclideanSpace ℝ (Fin 2)) × ℝ =>
      ContinuousPath.exitTime (ball (0 : EuclideanSpace ℝ (Fin 2)) p.2) p.1) := by
  have h := measurable_planarBall_exitTime_joint.comp
    ((continuous_eucPathToComplex.measurable.comp measurable_fst).prodMk measurable_snd)
  simpa only [Function.comp_def, exitTime_ball_eucPathToComplex] using h

end MatedCRT
