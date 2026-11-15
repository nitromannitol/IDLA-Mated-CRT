import MatedCRT.FirstPass.Derived.AreaCellPaperSourceEndpoint
import LatticeProb.Bonanno.BouRabeeGwynne.LevyProkhorovMaps

/-! # Exit-position and stopped-curve law comparison -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory HarmonicBalls LatticeProb BouRabeeGwynne
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand

/-- The distance from the paper's exit-position law to the endpoint law of a
comparison curve is bounded by the distance between their stopped-curve laws.
An infinite exit clock is evaluated at zero. -/
theorem areaCell_paper_exitPosition_le_sourceCurve
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (c : ℤ → ℤ → ℕ)
    {m : ℝ} (hm : 0 ≤ m) (a : ℝ) {U : Set ℂ} (hU : IsOpen U)
    (Q : Measure (ℕ → ℤ)) (ν : Measure (BouRabeeGwynne.CurveSpace 2)) :
    levyProkhorovEDist
      (Q.map (fun x => (a • interpPathCM (vertexPoint ε η) hm x)
        (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm x)).toNNReal))
      (ν.map (fun q => Complex.orthonormalBasisOneI.repr.symm (BouRabeeGwynne.CurveSpace.endPoint q))) ≤
    levyProkhorovEDist
      (Q.map (fun x => CurveSpaceComparison.isometryEquiv 2
        (normalizedPrefixCurve
          (complexToEuclideanPath (a • interpPathCM (vertexPoint ε η) hm x))
          (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm x)).toNNReal))) ν := by
  let f := fun q : BouRabeeGwynne.CurveSpace 2 =>
    Complex.orthonormalBasisOneI.repr.symm (BouRabeeGwynne.CurveSpace.endPoint q)
  let P := Q.map (fun x => CurveSpaceComparison.isometryEquiv 2
    (normalizedPrefixCurve
      (complexToEuclideanPath (a • interpPathCM (vertexPoint ε η) hm x))
      (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm x)).toNNReal))
  have hlaw : P.map f = Q.map (fun x =>
      (a • interpPathCM (vertexPoint ε η) hm x)
        (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm x)).toNNReal) := by
    have he := areaCell_relabelled_sourceCurve_endpoint_law h hε c hm a hU Q
    rw [areaCell_relabelled_sourceContinuousExitCurve_law h hε c hm a hU Q] at he
    exact he
  have hf : LipschitzWith 1 f := by
    change LipschitzWith 1 (Complex.orthonormalBasisOneI.repr.symm ∘
      BouRabeeGwynne.CurveSpace.endPoint)
    simpa only [one_mul] using
      (Complex.orthonormalBasisOneI.repr.symm.isometry.lipschitzWith.comp
        (BouRabeeGwynne.CurveSpace.endPoint_lipschitz (d := 2)))
  have hfm : Measurable f := hf.continuous.measurable
  have hb := BouRabeeGwynne.levyProkhorovEDist_map_le_of_lipschitz_one hf hfm P ν
  rw [hlaw] at hb
  exact hb

end MatedCRT
end
