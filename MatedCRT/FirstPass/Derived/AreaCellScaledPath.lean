import MatedCRT.FirstPass.Derived.AreaCellConstantStepLaw
import MatedCRT.FirstPass.Derived.PaperDomainExitClock
import LatticeProb.LQG.ShiftedGridWalkDilation

/-! # Scaled area-cell paths and exit clocks -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory ReflectedGMS ReflectedGMS.GMS LatticeProb HarmonicBalls
open LatticeProb.ReparamDistanceIsometry
open scoped NNReal

/-- Scaling the area-cell representatives scales the embedded paper path. -/
theorem areaCell_scaled_constantStepPath_eq
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (c : ℤ → ℤ → ℕ)
    {m : ℝ} (hm : 0 ≤ m) (a : ℝ) (x : ℕ → ℤ) :
    ConstantStepInterpolation.continuousPlanePath m
      (fun n => a • areaCellRepresentative h hε c (euclideanCellEquiv h hε (x n))) =
      complexToEuclideanPath (a • interpPathCM (vertexPoint ε η) hm x) := by
  apply ContinuousMap.ext
  intro t
  change ConstantStepInterpolation.path m
      (fun n => a • areaCellRepresentative h hε c (euclideanCellEquiv h hε (x n))) t =
    Complex.orthonormalBasisOneI.repr (a • interpPathCM (vertexPoint ε η) hm x t)
  rw [ConstantStepInterpolation.path_smul, map_smul]
  congr 1
  exact congrArg (fun f : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) => f t)
    (areaCell_constantStepPath_eq h hε c hm x)

/-- The scaled area-cell path and the complex embedded path have the same
continuous exit clock, including when the exit time is infinite. -/
theorem areaCell_scaled_continuousExitTime_eq
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (c : ℤ → ℤ → ℕ)
    {m : ℝ} (hm : 0 ≤ m) (a : ℝ) (x : ℕ → ℤ) (U : Set ℂ) :
    continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) 0
      (ConstantStepInterpolation.continuousPlanePath m
        (fun n => a • areaCellRepresentative h hε c (euclideanCellEquiv h hε (x n)))) =
      pathExitTime U (a • interpPathCM (vertexPoint ε η) hm x) := by
  exact (congrArg (continuousExitTime
    (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) 0)
    (areaCell_scaled_constantStepPath_eq h hε c hm a x)).trans
      (continuousExitTime_complexToEuclideanPath U _)

end MatedCRT
end
