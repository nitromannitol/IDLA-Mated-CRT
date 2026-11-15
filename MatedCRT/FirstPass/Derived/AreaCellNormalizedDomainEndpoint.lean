import MatedCRT.FirstPass.Derived.PlanarBrownianExitNormalization
import MatedCRT.FirstPass.Derived.AreaCellUniformPlanarBrownianEndpoint

/-! # Normalized-domain planar Brownian endpoint comparison -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set HarmonicBalls BouRabeeGwynne LatticeProb
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open scoped ENNReal NNReal

namespace MatedCRT

/-- Division by a positive real radius normalizes the planar exit law. -/
theorem planarBrownianExitProbability_normalize_div (U : Set ℂ) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (c z : ℂ) {r : ℝ} (hr : 0 < r) :
    let W := (fun w : ℂ => c + r • w) ⁻¹' U
    let hW : IsOpen W := hU.preimage (by fun_prop)
    ((planarBrownianExitProbability U hU z : ProbabilityMeasure ℂ) : Measure ℂ).map
        (fun w => (w - c) / (r : ℂ)) =
      ((planarBrownianExitProbability W hW ((z - c) / (r : ℂ)) : ProbabilityMeasure ℂ) :
        Measure ℂ) := by
  simpa only [div_eq_mul_inv, Complex.real_smul, Complex.ofReal_inv, mul_comm] using
    planarBrownianExitProbability_normalize U hU hUb c z hr


/-- A uniform stopped-curve bound controls normalized exit-position laws against
Brownian exit probabilities in the normalized domain. Infinite walk exit times
are evaluated at zero. -/
theorem iSup_areaCell_paper_normalized_exitPosition_normalizedPlanarBrownian_le
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (mult : ℤ → ℤ → ℕ)
    {m : ℝ} (hm : 0 ≤ m) (a : ℝ) {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (A : Set ℤ) (ρ : Measure (BouRabeeGwynne.BrownianPath 2))
    (hρ : BouRabeeGwynne.IsStandardBrownianLaw ρ) (c : ℂ) {r : ℝ} (hr : 0 < r)
    (B : ℝ≥0∞)
    (hcurve : ∀ x ∈ A, levyProkhorovEDist
      ((srwLaw mult x).map (fun w => CurveSpaceComparison.isometryEquiv 2
        (normalizedPrefixCurve
          (complexToEuclideanPath (a • interpPathCM (vertexPoint ε η) hm w))
          (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm w)).toNNReal)))
      (stoppedBrownianLaw (Complex.orthonormalBasisOneI.repr '' U)
        (Complex.orthonormalBasisOneI.repr (a • vertexPoint ε η x)) ρ) ≤ B) :
    let W := (fun w : ℂ => c + r • w) ⁻¹' U
    let hW : IsOpen W := hU.preimage (by fun_prop)
    ⨆ x ∈ A, levyProkhorovEDist
      (((srwLaw mult x).map (fun w => (a • interpPathCM (vertexPoint ε η) hm w)
        (pathExitTime U (a • interpPathCM (vertexPoint ε η) hm w)).toNNReal)).map
        (fun z : ℂ => (z - c) / (r : ℂ)))
      ((planarBrownianExitProbability W hW
        ((a • vertexPoint ε η x - c) / (r : ℂ)) : ProbabilityMeasure ℂ) : Measure ℂ) ≤
      ((max 1 (Real.toNNReal r⁻¹) : ℝ≥0) : ℝ≥0∞) * B := by
  dsimp only
  have hb := iSup_areaCell_paper_normalized_exitPosition_planarBrownian_le
    h hε mult hm a hU A ρ hρ c hr B hcurve
  simpa only [planarBrownianExitProbability_normalize_div U hU hUb c _ hr] using hb


end MatedCRT
end
