import MatedCRT.FirstPass.Derived.AreaCellParentInteriorFiniteExit
import MatedCRT.FirstPass.Derived.AreaCellRelabelledSourceCurveLaw
import MatedCRT.FirstPass.Derived.AreaCellLaw

/-! # Source-curve and exit data for area-cell walks -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne HarmonicBalls
open MatedCRTHarmonic MatedCRTHarmonic.GMSMain LatticeProb
open LatticeProb.ParentBlock LatticeProb.ReparamDistanceIsometry
open LatticeProb.UnboundedRayIntervalIntegrand
open scoped NNReal ENNReal

/-- The relabelled integer walk is a cell walk, has the paper's source-curve
law, and exits all parent-block interiors in finite time almost surely. -/
theorem MatedCRTEnv.areaCell_sourceLaw_and_parentBlock_exit
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    {μ : Measure ℂ} (h : IsAreaParametrized μ (S.η ω))
    {ε : ℝ} (hε : 0 < ε)
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
    (hmult : IsLocallyFiniteMult (S.mult ε ω))
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf) (0 : ℤ))
    (hH : H.cell = cell ε (S.η ω))
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf).adj.Connected)
    {σ : ℝ≥0} (hσ : 0 < σ)
    (hcell : (areaCellConfig h hε (S.mult ε ω)).IsCellConfiguration)
    (hadj : ∀ K : (areaCellConfig h hε (S.mult ε ω)).cells,
      ∃ K' : (areaCellConfig h hε (S.mult ε ω)).cells,
        (areaCellConfig h hε (S.mult ε ω)).Adj K K')
    (hrec : (areaCellConfig h hε (S.mult ε ω)).Recurrent) (x : ℤ)
    {m : ℝ} (hm : 0 ≤ m) {U : Set ℂ} (hU : IsOpen U) :
    let C := areaCellConfig h hε (S.mult ε ω)
    let e := euclideanCellEquiv h hε
    let p := areaCellRepresentative h hε (S.mult ε ω)
    let Q := (srwLaw (S.mult ε ω) x).map (fun ξ n => e (ξ n))
    C.IsSRWLaw (e x) Q ∧
    Q.map (fun y => CurveSpaceComparison.isometryEquiv 2
      (normalizedPrefixCurve
        (ConstantStepInterpolation.continuousPlanePath m (fun n => (σ : ℝ) • p (y n)))
        (LatticeProb.continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) 0
          (ConstantStepInterpolation.continuousPlanePath m
            (fun n => (σ : ℝ) • p (y n)))).toNNReal)) =
    (srwLaw (S.mult ε ω) x).map (fun y => CurveSpaceComparison.isometryEquiv 2
      (normalizedPrefixCurve
        (complexToEuclideanPath ((σ : ℝ) • interpPathCM (vertexPoint ε (S.η ω)) hm y))
        (pathExitTime U ((σ : ℝ) • interpPathCM (vertexPoint ε (S.η ω)) hm y)).toNNReal)) ∧
    ∀ᵐ ξ ∂Q, ∀ (c : ℂ) (a : ℝ), 0 ≤ a →
      BouRabeeGwynne.continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (parentBlock c a)) 0 (C.interpolatedWalk p σ ξ) ≠ ∞ := by
  refine ⟨S.areaCellConfig_isSRWLaw ω h hε hmult x, ?_, ?_⟩
  · exact areaCell_relabelled_sourceContinuousExitCurve_law h hε (S.mult ε ω)
      hm (σ : ℝ) hU (srwLaw (S.mult ε ω) x)
  · exact S.ae_continuousExitTime_ne_top_all_parentBlock_interior ω h hε hlf hmult
      H hH hconn hσ hcell hadj hrec x

end MatedCRT
end
