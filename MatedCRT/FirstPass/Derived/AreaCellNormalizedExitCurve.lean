import MatedCRT.FirstPass.Derived.AreaCellScaledPath
import MatedCRT.FirstPass.Derived.PaperNormalizedCurveLaw

/-! # Normalized continuous exit curves of area-cell walks -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory HarmonicBalls LatticeProb
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand

/-- The scaled area-cell and paper paths give the same normalized continuous
exit curve, including the totalized infinite-exit case. -/
theorem areaCell_scaled_normalizedExitCurve_eq
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (c : ℤ → ℤ → ℕ)
    {m : ℝ} (hm : 0 ≤ m) (a : ℝ) (x : ℕ → ℤ) (U : Set ℂ) :
    normalizedPrefixCurve
      (ConstantStepInterpolation.continuousPlanePath m
        (fun n => a • areaCellRepresentative h hε c (euclideanCellEquiv h hε (x n))))
      (continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) 0
        (ConstantStepInterpolation.continuousPlanePath m
          (fun n => a • areaCellRepresentative h hε c (euclideanCellEquiv h hε (x n))))).toNNReal =
    normalizedPrefixCurve (complexToEuclideanPath (a • interpPathCM (vertexPoint ε η) hm x))
      (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm x)).toNNReal := by
  rw [areaCell_scaled_continuousExitTime_eq h hε c hm a x U,
    areaCell_scaled_constantStepPath_eq h hε c hm a x]

/-- The normalized continuous exit curve is measurable on integer paths. -/
theorem measurable_areaCell_scaled_normalizedExitCurve
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (c : ℤ → ℤ → ℕ)
    {m : ℝ} (hm : 0 ≤ m) (a : ℝ) {U : Set ℂ} (hU : IsOpen U) :
    Measurable (fun x : ℕ → ℤ =>
      normalizedPrefixCurve
        (ConstantStepInterpolation.continuousPlanePath m
          (fun n => a • areaCellRepresentative h hε c (euclideanCellEquiv h hε (x n))))
        (continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) 0
          (ConstantStepInterpolation.continuousPlanePath m
            (fun n => a • areaCellRepresentative h hε c (euclideanCellEquiv h hε (x n))))).toNNReal) := by
  have hp : Measurable (fun x : ℕ → ℤ => a • interpPathCM (vertexPoint ε η) hm x) :=
    ((continuous_interpPathCM (vertexPoint ε η) hm).const_smul a).measurable
  have hcurve := (measurable_paperNormalizedExitCurve hU).comp hp
  convert hcurve using 1
  funext x
  exact areaCell_scaled_normalizedExitCurve_eq h hε c hm a x U

/-- The two descriptions induce the same normalized continuous exit-curve law. -/
theorem areaCell_scaled_normalizedExitCurve_map
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (c : ℤ → ℤ → ℕ)
    {m : ℝ} (hm : 0 ≤ m) (a : ℝ) (U : Set ℂ) (Q : Measure (ℕ → ℤ)) :
    Q.map (fun x => normalizedPrefixCurve
      (ConstantStepInterpolation.continuousPlanePath m
        (fun n => a • areaCellRepresentative h hε c (euclideanCellEquiv h hε (x n))))
      (continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) 0
        (ConstantStepInterpolation.continuousPlanePath m
          (fun n => a • areaCellRepresentative h hε c (euclideanCellEquiv h hε (x n))))).toNNReal) =
    Q.map (fun x => normalizedPrefixCurve
      (complexToEuclideanPath (a • interpPathCM (vertexPoint ε η) hm x))
      (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm x)).toNNReal) := by
  congr 1
  funext x
  exact areaCell_scaled_normalizedExitCurve_eq h hε c hm a x U

end MatedCRT
end
