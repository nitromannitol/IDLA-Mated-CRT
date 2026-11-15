import MatedCRT.FirstPass.Derived.AreaCellRepresentative
import MatedCRT.FirstPass.Derived.ComplexWalkAffineInterpolation
import MatedCRT.FirstPass.Derived.InterpolatedWalkPath
import LatticeProb.Walk.CellConfigVisitPathLaw
import LatticeProb.Topology.ReparamDistanceIsometry

/-! # Constant-step paths on curve cells -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory ReflectedGMS ReflectedGMS.GMS
open LatticeProb.ReparamDistanceIsometry
open scoped NNReal

/-- The constant-step path of endpoint representatives is the embedded integer
walk read in Euclidean coordinates. -/
theorem areaCell_constantStepPath_eq
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (c : ℤ → ℤ → ℕ)
    {m : ℝ} (hm : 0 ≤ m) (x : ℕ → ℤ) :
    LatticeProb.ConstantStepInterpolation.continuousPlanePath m
      (fun n => areaCellRepresentative h hε c (euclideanCellEquiv h hε (x n))) =
      complexToEuclideanPath (interpPathCM (vertexPoint ε η) hm x) := by
  apply ContinuousMap.ext
  intro t
  change LatticeProb.ConstantStepInterpolation.path m
    (fun n => areaCellRepresentative h hε c (euclideanCellEquiv h hε (x n))) t =
    Complex.orthonormalBasisOneI.repr (interpolatedWalk ε η m x t)
  rw [repr_interpolatedWalk]
  simp only [LatticeProb.ConstantStepInterpolation.path, areaCellRepresentative_equiv]

/-- The two path representations induce the same law for any measure on
integer trajectories. -/
theorem areaCell_constantStepPath_map
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (c : ℤ → ℤ → ℕ)
    {m : ℝ} (hm : 0 ≤ m) (Q : Measure (ℕ → ℤ)) :
    Q.map (fun x => LatticeProb.ConstantStepInterpolation.continuousPlanePath m
      (fun n => areaCellRepresentative h hε c (euclideanCellEquiv h hε (x n)))) =
      Q.map (fun x => complexToEuclideanPath (interpPathCM (vertexPoint ε η) hm x)) := by
  congr 1
  funext x
  exact areaCell_constantStepPath_eq h hε c hm x

end MatedCRT
end
