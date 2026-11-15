import MatedCRT.FirstPass.Derived.AreaCellPaperMappedEndpointComparison
import MatedCRT.Defs.RandomWalk
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveLaws

/-! # Uniform normalized paper walk and Brownian endpoint comparison -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory HarmonicBalls LatticeProb BouRabeeGwynne
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open scoped NNReal ENNReal

/-- A common bound on stopped-curve distances controls the normalized endpoint
law distances uniformly over the same set of paper walk starting vertices.
Infinite walk exit times are evaluated at zero. -/
theorem iSup_areaCell_paper_normalized_exitPosition_brownian_le
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (mult : ℤ → ℤ → ℕ)
    {m : ℝ} (hm : 0 ≤ m) (a : ℝ) {U : Set ℂ} (hU : IsOpen U)
    (A : Set ℤ) (ρ : Measure (BouRabeeGwynne.BrownianPath 2)) (c : ℂ) {r : ℝ} (hr : 0 < r)
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
      (((stoppedBrownianLaw (Complex.orthonormalBasisOneI.repr '' U)
        (Complex.orthonormalBasisOneI.repr (a • vertexPoint ε η x)) ρ).map
        (fun q => Complex.orthonormalBasisOneI.repr.symm (BouRabeeGwynne.CurveSpace.endPoint q))).map
        (fun z : ℂ => (z - c) / (r : ℂ))) ≤
      ((max 1 (Real.toNNReal r⁻¹) : ℝ≥0) : ℝ≥0∞) * B := by
  refine iSup_le fun x => iSup_le fun hx => ?_
  exact (areaCell_paper_normalized_exitPosition_le_sourceCurve h hε mult hm a hU
    (srwLaw mult x) (stoppedBrownianLaw (Complex.orthonormalBasisOneI.repr '' U)
      (Complex.orthonormalBasisOneI.repr (a • vertexPoint ε η x)) ρ) c hr).trans
    (mul_le_mul_right (hcurve x hx) _)

end MatedCRT
end
