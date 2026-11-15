import MatedCRT.FirstPass.Derived.AreaCellPaperEndpointComparison
import MatedCRT.FirstPass.Derived.BrownianExitLawIdentification

/-! # Euclidean paper walk and Brownian endpoint laws -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory HarmonicBalls LatticeProb BouRabeeGwynne
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open scoped NNReal ENNReal

/-- The Euclidean exit-position law of the paper walk is controlled by the
corresponding stopped-curve law distance. Infinite exit clocks are evaluated
at time zero. -/
theorem areaCell_paper_euclidean_exitPosition_le_sourceCurve
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (mult : ℤ → ℤ → ℕ)
    {m : ℝ} (hm : 0 ≤ m) (a : ℝ) {U : Set ℂ} (hU : IsOpen U)
    (x : ℤ) (ρ : Measure (BouRabeeGwynne.BrownianPath 2)) :
    levyProkhorovEDist
      ((srwLaw mult x).map (fun w => Complex.orthonormalBasisOneI.repr
        ((a • interpPathCM (vertexPoint ε η) hm w)
          (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm w)).toNNReal)))
      ((stoppedBrownianLaw (Complex.orthonormalBasisOneI.repr '' U)
        (Complex.orthonormalBasisOneI.repr (a • vertexPoint ε η x)) ρ).map
          BouRabeeGwynne.CurveSpace.endPoint) ≤
    levyProkhorovEDist
      ((srwLaw mult x).map (fun w => CurveSpaceComparison.isometryEquiv 2
        (normalizedPrefixCurve
          (complexToEuclideanPath (a • interpPathCM (vertexPoint ε η) hm w))
          (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm w)).toNNReal)))
      (stoppedBrownianLaw (Complex.orthonormalBasisOneI.repr '' U)
        (Complex.orthonormalBasisOneI.repr (a • vertexPoint ε η x)) ρ) := by
  let R := Complex.orthonormalBasisOneI.repr
  let P := (srwLaw mult x).map (fun w =>
    (a • interpPathCM (vertexPoint ε η) hm w)
      (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm w)).toNNReal)
  let ν := stoppedBrownianLaw (R '' U) (R (a • vertexPoint ε η x)) ρ
  let Q := ν.map (fun q => R.symm (BouRabeeGwynne.CurveSpace.endPoint q))
  have hb := areaCell_paper_exitPosition_le_sourceCurve h hε mult hm a hU
    (srwLaw mult x) ν
  change levyProkhorovEDist P Q ≤ _ at hb
  have hc := BouRabeeGwynne.levyProkhorovEDist_map_le_of_lipschitz_one
    R.isometry.lipschitzWith R.continuous.measurable P Q
  have hp : P.map R = (srwLaw mult x).map (fun w => R
      ((a • interpPathCM (vertexPoint ε η) hm w)
        (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm w)).toNNReal)) := by
    have hpath : Measurable (fun w : ℕ → ℤ => a • interpPathCM (vertexPoint ε η) hm w) :=
      ((continuous_interpPathCM (vertexPoint ε η) hm).const_smul a).measurable
    have hexit : Measurable (fun f : C(ℝ≥0, ℂ) => f (pathExitTime U f).toNNReal) := by
      exact ContinuousEval.continuous_eval.measurable.comp
        (measurable_id.prodMk (ENNReal.measurable_toNNReal.comp
          (ExitTimeCdf.measurable_pathExitTime hU)))
    exact Measure.map_map R.continuous.measurable (hexit.comp hpath)
  have hq : Q.map R = ν.map BouRabeeGwynne.CurveSpace.endPoint := by
    change (ν.map (R.symm ∘ BouRabeeGwynne.CurveSpace.endPoint)).map R = _
    rw [Measure.map_map R.continuous.measurable
      (R.symm.continuous.measurable.comp BouRabeeGwynne.CurveSpace.continuous_endPoint.measurable)]
    congr 1
    funext q
    exact R.apply_symm_apply _
  rw [hp, hq] at hc
  exact hc.trans hb

end MatedCRT
end
