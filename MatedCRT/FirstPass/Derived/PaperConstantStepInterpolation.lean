import MatedCRT.FirstPass.Derived.ComplexWalkAffineInterpolation
import MatedCRT.FirstPass.Derived.InterpolatedWalkPath
import LatticeProb.Walk.CellConfigVisitPathLaw
import LatticeProb.Topology.ReparamDistanceIsometry

/-! # Constant-step interpolation of embedded walks -/

set_option autoImplicit false

noncomputable section

open scoped NNReal

namespace MatedCRT

/-- The embedded walk in Euclidean coordinates is the constant-step
interpolation through its embedded integer vertices. -/
theorem repr_interpolatedWalk_eq_constantStep
    (ε m : ℝ) (η : ℝ → ℂ) (x : ℕ → ℤ) (t : ℝ≥0) :
    Complex.orthonormalBasisOneI.repr (interpolatedWalk ε η m x t) =
      LatticeProb.ConstantStepInterpolation.path m
        (fun n => Complex.orthonormalBasisOneI.repr (η (ε * x n))) t := by
  rw [repr_interpolatedWalk]
  rfl

/-- The continuous path of an embedded walk agrees with its Euclidean
constant-step interpolation. -/
theorem complexToEuclideanPath_interpPathCM_eq_constantStep
    (ε : ℝ) (η : ℝ → ℂ) {m : ℝ} (hm : 0 ≤ m) (x : ℕ → ℤ) :
    LatticeProb.ReparamDistanceIsometry.complexToEuclideanPath
        (interpPathCM (vertexPoint ε η) hm x) =
      LatticeProb.ConstantStepInterpolation.continuousPlanePath m
        (fun n => Complex.orthonormalBasisOneI.repr (η (ε * x n))) := by
  apply ContinuousMap.ext
  intro t
  exact repr_interpolatedWalk_eq_constantStep ε m η x t

end MatedCRT
end
