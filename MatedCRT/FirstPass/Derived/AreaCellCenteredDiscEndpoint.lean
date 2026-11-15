import MatedCRT.FirstPass.Derived.AreaCellUniformPlanarBrownianEndpoint
import MatedCRT.FirstPass.Derived.NormalizedPlanarBrownianCenteredDisc

/-! # Centered disc exit comparison for area-cell walks -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls HarmonicBalls.Section6 LatticeProb BouRabeeGwynne
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open scoped NNReal ENNReal

/-- A uniform stopped-curve bound on discs centered at the respective walk
starts controls the normalized exit-position laws against the angular law.
Infinite walk exit times are evaluated at zero. -/
theorem iSup_areaCell_centeredDisc_normalized_exitPosition_le
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (mult : ℤ → ℤ → ℕ)
    {m : ℝ} (hm : 0 ≤ m) (a : ℝ) (A : Set ℤ)
    (ρ : Measure (BouRabeeGwynne.BrownianPath 2))
    (hρ : BouRabeeGwynne.IsStandardBrownianLaw ρ) {r : ℝ} (hr : 0 < r)
    (B : ℝ≥0∞)
    (hcurve : ∀ x ∈ A, let c := a • vertexPoint ε η x
      levyProkhorovEDist
        ((srwLaw mult x).map (fun w => CurveSpaceComparison.isometryEquiv 2
          (normalizedPrefixCurve
            (complexToEuclideanPath (a • interpPathCM (vertexPoint ε η) hm w))
            (pathExitTime (ball c r) (a • interpPathCM (vertexPoint ε η) hm w)).toNNReal)))
        (stoppedBrownianLaw (Complex.orthonormalBasisOneI.repr '' ball c r)
          (Complex.orthonormalBasisOneI.repr c) ρ) ≤ B) :
    (⨆ x ∈ A, let c := a • vertexPoint ε η x
      levyProkhorovEDist
        (((srwLaw mult x).map (fun w => (a • interpPathCM (vertexPoint ε η) hm w)
          (pathExitTime (ball c r) (a • interpPathCM (vertexPoint ε η) hm w)).toNNReal)).map
          (fun z : ℂ => (z - c) / (r : ℂ)))
        (normalizedCircleMeasure 0 1)) ≤
      ((max 1 (Real.toNNReal r⁻¹) : ℝ≥0) : ℝ≥0∞) * B := by
  refine iSup_le fun x => iSup_le fun hx => ?_
  let c := a • vertexPoint ε η x
  have hc : ∀ y ∈ ({x} : Set ℤ), levyProkhorovEDist
      ((srwLaw mult y).map (fun w => CurveSpaceComparison.isometryEquiv 2
        (normalizedPrefixCurve
          (complexToEuclideanPath (a • interpPathCM (vertexPoint ε η) hm w))
          (pathExitTime (ball c r) (a • interpPathCM (vertexPoint ε η) hm w)).toNNReal)))
      (stoppedBrownianLaw (Complex.orthonormalBasisOneI.repr '' ball c r)
        (Complex.orthonormalBasisOneI.repr (a • vertexPoint ε η y)) ρ) ≤ B := by
    intro y hy
    have : y = x := Set.mem_singleton_iff.mp hy
    subst y
    exact hcurve x hx
  have hb := iSup_areaCell_paper_normalized_exitPosition_planarBrownian_le
    h hε mult hm a (isOpen_ball : IsOpen (ball c r)) {x} ρ hρ c hr B hc
  have hpoint := (le_iSup_of_le x (le_iSup_of_le (Set.mem_singleton x) le_rfl)).trans hb
  have hnorm := planarBrownianExitProbability_ball_center_normalize c hr
  have hnorm' :
      ((planarBrownianExitProbability (ball c r) isOpen_ball c : ProbabilityMeasure ℂ) :
        Measure ℂ).map (fun w => (w - c) / (r : ℂ)) = normalizedCircleMeasure 0 1 := by
    simpa only [div_eq_mul_inv, Complex.real_smul, Complex.ofReal_inv, mul_comm] using hnorm
  dsimp only [c] at hnorm' hpoint ⊢
  rw [hnorm'] at hpoint
  exact hpoint

end MatedCRT
end
