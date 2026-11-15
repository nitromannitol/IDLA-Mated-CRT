import MatedCRT.FirstPass.Derived.AreaCellRelabelledSourceCurveLaw
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveLaws

/-! # Endpoint laws of area-cell source curves -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory HarmonicBalls LatticeProb
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand

/-- The endpoint law of the relabelled area-cell source curve is the law of the
paper's scaled embedded walk evaluated at its continuous exit clock. An infinite
clock is evaluated at zero. -/
theorem areaCell_relabelled_sourceCurve_endpoint_law
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (c : ℤ → ℤ → ℕ)
    {m : ℝ} (hm : 0 ≤ m) (a : ℝ) {U : Set ℂ} (hU : IsOpen U)
    (Q : Measure (ℕ → ℤ)) :
    ((Q.map (fun x n => euclideanCellEquiv h hε (x n))).map
      (fun y => CurveSpaceComparison.isometryEquiv 2
        (normalizedPrefixCurve
          (ConstantStepInterpolation.continuousPlanePath m
            (fun n => a • areaCellRepresentative h hε c (y n)))
          (continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) 0
            (ConstantStepInterpolation.continuousPlanePath m
              (fun n => a • areaCellRepresentative h hε c (y n)))).toNNReal))).map
      (fun q => Complex.orthonormalBasisOneI.repr.symm
        (BouRabeeGwynne.CurveSpace.endPoint q)) =
    Q.map (fun x => (a • interpPathCM (vertexPoint ε η) hm x)
      (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm x)).toNNReal) := by
  rw [areaCell_relabelled_sourceContinuousExitCurve_law h hε c hm a hU Q]
  have hp : Measurable (fun x : ℕ → ℤ => a • interpPathCM (vertexPoint ε η) hm x) :=
    ((continuous_interpPathCM (vertexPoint ε η) hm).const_smul a).measurable
  have hc : Measurable (fun x : ℕ → ℤ => CurveSpaceComparison.isometryEquiv 2
      (normalizedPrefixCurve
        (complexToEuclideanPath (a • interpPathCM (vertexPoint ε η) hm x))
        (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm x)).toNNReal)) :=
    (CurveSpaceComparison.isometryEquiv 2).continuous.measurable.comp
      ((measurable_paperNormalizedExitCurve hU).comp hp)
  change (Q.map (fun x => CurveSpaceComparison.isometryEquiv 2
      (normalizedPrefixCurve
        (complexToEuclideanPath (a • interpPathCM (vertexPoint ε η) hm x))
        (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm x)).toNNReal))).map
      (Complex.orthonormalBasisOneI.repr.symm ∘ BouRabeeGwynne.CurveSpace.endPoint) = _
  rw [Measure.map_map (Complex.orthonormalBasisOneI.repr.symm.continuous.measurable.comp
    BouRabeeGwynne.CurveSpace.continuous_endPoint.measurable) hc]
  congr 1
  funext x
  change Complex.orthonormalBasisOneI.repr.symm (CurveSpace.endPoint
    (normalizedPrefixCurve (complexToEuclideanPath (a • interpPathCM (vertexPoint ε η) hm x))
      (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm x)).toNNReal)) = _
  rw [normalizedPrefixCurve_endPoint]
  simp [complexToEuclideanPath]

end MatedCRT
end
