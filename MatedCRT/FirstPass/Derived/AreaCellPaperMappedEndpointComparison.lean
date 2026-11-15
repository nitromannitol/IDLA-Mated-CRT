import MatedCRT.FirstPass.Derived.AreaCellPaperEndpointComparison
import LatticeProb.Prob.LevyProkhorovLipschitz
import LatticeProb.Prob.AffineSourceFrontier

/-! # Spatial images of paper exit-position laws -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory HarmonicBalls LatticeProb BouRabeeGwynne
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open scoped NNReal ENNReal

/-- A Lipschitz spatial map transfers the stopped-curve comparison to the
corresponding image exit-position laws. Infinite exit clocks are evaluated at
zero. -/
theorem areaCell_paper_mapped_exitPosition_le_sourceCurve
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (c : ℤ → ℤ → ℕ)
    {m : ℝ} (hm : 0 ≤ m) (a : ℝ) {U : Set ℂ} (hU : IsOpen U)
    (Q : Measure (ℕ → ℤ)) (ν : Measure (BouRabeeGwynne.CurveSpace 2))
    {Y : Type*} [PseudoEMetricSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {K : ℝ≥0} {f : ℂ → Y} (hf : LipschitzWith K f) (hfm : Measurable f) :
    levyProkhorovEDist
      ((Q.map (fun x => (a • interpPathCM (vertexPoint ε η) hm x)
        (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm x)).toNNReal)).map f)
      ((ν.map (fun q => Complex.orthonormalBasisOneI.repr.symm
        (BouRabeeGwynne.CurveSpace.endPoint q))).map f) ≤
    ((max 1 K : ℝ≥0) : ℝ≥0∞) *
      levyProkhorovEDist
        (Q.map (fun x => CurveSpaceComparison.isometryEquiv 2
          (normalizedPrefixCurve
            (complexToEuclideanPath (a • interpPathCM (vertexPoint ε η) hm x))
            (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm x)).toNNReal))) ν := by
  have hmap := levyProkhorovEDist_map_le_of_lipschitz (le_max_left 1 K)
    (hf.weaken (le_max_right 1 K)) hfm
    (Q.map (fun x => (a • interpPathCM (vertexPoint ε η) hm x)
      (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm x)).toNNReal))
    (ν.map (fun q => Complex.orthonormalBasisOneI.repr.symm
      (BouRabeeGwynne.CurveSpace.endPoint q)))
  apply hmap.trans
  gcongr
  exact areaCell_paper_exitPosition_le_sourceCurve h hε c hm a hU Q ν

/-- Affine normalization gives the corresponding exit-law comparison in
coordinates centered at `c` and scaled by the positive radius `r`. -/
theorem areaCell_paper_normalized_exitPosition_le_sourceCurve
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (mult : ℤ → ℤ → ℕ)
    {m : ℝ} (hm : 0 ≤ m) (a : ℝ) {U : Set ℂ} (hU : IsOpen U)
    (Q : Measure (ℕ → ℤ)) (ν : Measure (BouRabeeGwynne.CurveSpace 2))
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    levyProkhorovEDist
      ((Q.map (fun x => (a • interpPathCM (vertexPoint ε η) hm x)
        (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm x)).toNNReal)).map
        (fun z : ℂ => (z - c) / (r : ℂ)))
      ((ν.map (fun q => Complex.orthonormalBasisOneI.repr.symm
        (BouRabeeGwynne.CurveSpace.endPoint q))).map (fun z : ℂ => (z - c) / (r : ℂ))) ≤
    ((max 1 (Real.toNNReal r⁻¹) : ℝ≥0) : ℝ≥0∞) *
      levyProkhorovEDist
        (Q.map (fun x => CurveSpaceComparison.isometryEquiv 2
          (normalizedPrefixCurve
            (complexToEuclideanPath (a • interpPathCM (vertexPoint ε η) hm x))
            (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm x)).toNNReal))) ν := by
  have hf : LipschitzWith (Real.toNNReal r⁻¹) (fun z : ℂ => (z - c) / (r : ℂ)) := by
    have hl := Complex.orthonormalBasisOneI.repr.symm.isometry.lipschitzWith.comp
      ((affinePlaneNormalization_lipschitz c hr).comp
        Complex.orthonormalBasisOneI.repr.isometry.lipschitzWith)
    simpa [affinePlaneNormalization, Function.comp_def] using hl
  exact areaCell_paper_mapped_exitPosition_le_sourceCurve h hε mult hm a hU Q ν hf
    hf.continuous.measurable

end MatedCRT
end
