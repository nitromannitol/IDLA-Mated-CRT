import MatedCRT.FirstPass.Derived.AreaCellUniformPaperBrownianEndpoint
import MatedCRT.FirstPass.Derived.BrownianExitLawIdentification
import MatedCRT.Defs.RandomWalk
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveLaws

/-! # Uniform normalized paper walk and planar Brownian exit laws -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory HarmonicBalls LatticeProb BouRabeeGwynne
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open scoped NNReal ENNReal

/-- A common bound on stopped-curve distances controls the normalized endpoint
law distances uniformly over the same set of paper walk starting vertices.
Infinite walk exit times are evaluated at zero. -/
theorem iSup_areaCell_paper_normalized_exitPosition_planarBrownian_le
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (mult : ℤ → ℤ → ℕ)
    {m : ℝ} (hm : 0 ≤ m) (a : ℝ) {U : Set ℂ} (hU : IsOpen U)
    (A : Set ℤ) (ρ : Measure (BouRabeeGwynne.BrownianPath 2))
    (hρ : BouRabeeGwynne.IsStandardBrownianLaw ρ) (c : ℂ) {r : ℝ} (hr : 0 < r)
    (B : ℝ≥0∞)
    (hcurve : ∀ x ∈ A, levyProkhorovEDist
      ((srwLaw mult x).map (fun w => CurveSpaceComparison.isometryEquiv 2
        (normalizedPrefixCurve
          (complexToEuclideanPath (a • interpPathCM (vertexPoint ε η) hm w))
          (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm w)).toNNReal)))
      (stoppedBrownianLaw (Complex.orthonormalBasisOneI.repr '' U)
        (Complex.orthonormalBasisOneI.repr (a • vertexPoint ε η x)) ρ) ≤ B) :
    ⨆ x ∈ A, levyProkhorovEDist
      (((srwLaw mult x).map (fun w => (a • interpPathCM (vertexPoint ε η) hm w)
        (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm w)).toNNReal)).map
        (fun z : ℂ => (z - c) / (r : ℂ)))
      (((planarBrownianExitProbability U hU (a • vertexPoint ε η x) :
        ProbabilityMeasure ℂ) : Measure ℂ).map (fun z : ℂ => (z - c) / (r : ℂ))) ≤
      ((max 1 (Real.toNNReal r⁻¹) : ℝ≥0) : ℝ≥0∞) * B := by
  have heq (z : ℂ) :
      ((stoppedBrownianLaw (Complex.orthonormalBasisOneI.repr '' U)
        (Complex.orthonormalBasisOneI.repr z) ρ).map
          (fun q => Complex.orthonormalBasisOneI.repr.symm
            (BouRabeeGwynne.CurveSpace.endPoint q))) =
        ((planarBrownianExitProbability U hU z : ProbabilityMeasure ℂ) : Measure ℂ) := by
    change (stoppedBrownianLaw (Complex.orthonormalBasisOneI.repr '' U)
      (Complex.orthonormalBasisOneI.repr z) ρ).map
      (Complex.orthonormalBasisOneI.repr.symm ∘ BouRabeeGwynne.CurveSpace.endPoint) = _
    rw [← Measure.map_map Complex.orthonormalBasisOneI.repr.symm.continuous.measurable
      BouRabeeGwynne.CurveSpace.continuous_endPoint.measurable,
      BrownianExitLawIdentification.stoppedBrownianLaw_endPoint_eq U hU z ρ hρ,
      Measure.map_map Complex.orthonormalBasisOneI.repr.symm.continuous.measurable
        Complex.orthonormalBasisOneI.repr.continuous.measurable]
    have hid : (Complex.orthonormalBasisOneI.repr.symm ∘
        Complex.orthonormalBasisOneI.repr) = id := by
      funext w
      exact Complex.orthonormalBasisOneI.repr.symm_apply_apply w
    rw [hid, Measure.map_id]
  have hb := iSup_areaCell_paper_normalized_exitPosition_brownian_le
    h hε mult hm a hU A ρ c hr B hcurve
  simpa only [heq] using hb

end MatedCRT
end
