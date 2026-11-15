import MatedCRT.FirstPass.Derived.AreaCellScaledPath

/-! # Distances between area-cell exit and vertex-prefix curves -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory HarmonicBalls LatticeProb
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open scoped NNReal ENNReal

/-- The paper's stopped complex ray and an arbitrary finite prefix of the same
scaled walk have the distance of the corresponding Euclidean area-cell curves.
The prefix time may be an exterior-vertex knot, which need not be the
continuous exit time. -/
theorem areaCell_exit_prefix_distance_eq
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (c : ℤ → ℤ → ℕ)
    {m : ℝ} (hm : 0 ≤ m) (a : ℝ) (x : ℕ → ℤ)
    (U : Set ℂ) (T : ℝ≥0)
    (hfin : pathExitTime U (a • interpPathCM (vertexPoint ε η) hm x) ≠ ⊤) :
    cmpEDist (stopAtExit U (a • interpPathCM (vertexPoint ε η) hm x))
      (fun t => (a • interpPathCM (vertexPoint ε η) hm x) (min t T)) =
    edist (normalizedPrefixCurve
      (ConstantStepInterpolation.continuousPlanePath m
        (fun n => a • areaCellRepresentative h hε c (euclideanCellEquiv h hε (x n))))
      (continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) 0
        (ConstantStepInterpolation.continuousPlanePath m
          (fun n => a • areaCellRepresentative h hε c (euclideanCellEquiv h hε (x n))))).toNNReal)
      (normalizedPrefixCurve
        (ConstantStepInterpolation.continuousPlanePath m
          (fun n => a • areaCellRepresentative h hε c (euclideanCellEquiv h hε (x n)))) T) := by
  rw [areaCell_scaled_continuousExitTime_eq h hε c hm a x U,
    areaCell_scaled_constantStepPath_eq h hε c hm a x]
  have hs : stopAtExit U (a • interpPathCM (vertexPoint ε η) hm x) =
      fun t => (a • interpPathCM (vertexPoint ε η) hm x)
        (min t (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm x)).toNNReal) := by
    funext t
    simp [stopAtExit, hfin]
  rw [hs]
  exact complex_stoppedRay_eq_normalizedPrefixCurve _ _ _ _

end MatedCRT
end
