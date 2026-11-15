import MatedCRT.FirstPass.Derived.AreaCellParentInteriorFiniteExit
import MatedCRT.FirstPass.Derived.AreaCellLaw
import LatticeProb.Prob.WalkBrownianParentFrontier

/-! # Area-cell walk and Brownian parent-frontier distances -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic MatedCRTHarmonic.GMSMain
open LatticeProb LatticeProb.CellConfigWalk LatticeProb.CellConfigInterpolation
open LatticeProb.CellConfigCappedSquare
open scoped NNReal ENNReal

/-- The parent-frontier distance between the area-cell walk and Brownian exit
laws agrees with the distance between their normalized ambient exit laws. -/
theorem MatedCRTEnv.areaCell_parentFrontier_distance
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    {μ : Measure ℂ} (h : IsAreaParametrized μ (S.η ω))
    {ε : ℝ} (hε : 0 < ε)
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
    (hm : IsLocallyFiniteMult (S.mult ε ω))
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf) (0 : ℤ))
    (hH : H.cell = cell ε (S.η ω))
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf).adj.Connected)
    {σ : ℝ≥0} (hσ : 0 < σ)
    (hcell : (areaCellConfig h hε (S.mult ε ω)).IsCellConfiguration)
    (hadj : ∀ K : (areaCellConfig h hε (S.mult ε ω)).cells,
      ∃ K' : (areaCellConfig h hε (S.mult ε ω)).cells,
        (areaCellConfig h hε (S.mult ε ω)).Adj K K')
    (hrec : (areaCellConfig h hε (S.mult ε ω)).Recurrent) (x : ℤ)
    (c : ℂ) {a : ℝ} (ha : 0 < a)
    (hstart : planeCoord.symm ((σ : ℝ) •
      areaCellRepresentative h hε (S.mult ε ω) (euclideanCellEquiv h hε x)) ∈
      ParentBlock.closedSquare c a)
    (ρ : Measure (BouRabeeGwynne.BrownianPath 2)) (hρ : BouRabeeGwynne.IsStandardBrownianLaw ρ) :
    let C := areaCellConfig h hε (S.mult ε ω)
    let p := areaCellRepresentative h hε (S.mult ε ω)
    let K := euclideanCellEquiv h hε x
    let Q := (srwLaw (S.mult ε ω) x).map (fun ξ n => euclideanCellEquiv h hε (ξ n))
    let U := planeCoord.symm ⁻¹' interior (ParentBlock.parentBlock c a)
    let ν := ((stoppedBrownianLaw U ((σ : ℝ) • p K) ρ).map
      BouRabeeGwynne.CurveSpace.endPoint).map planeCoord.symm
    let μ := Q.map (fun ξ => planeCoord.symm ((C.interpolatedWalk p σ ξ)
      (BouRabeeGwynne.continuousExitTime U 0 (C.interpolatedWalk p σ ξ)).toNNReal))
    letI : MetricSpace MetricPlane := normalizedPlaneMetric c a ha.ne'
    let F : Set MetricPlane := MetricPlane.down ⁻¹' frontier (ParentBlock.parentBlock c a)
    levyProkhorovEDist ((μ.map MetricPlane.up).comap ((↑) : F → MetricPlane))
        ((ν.map MetricPlane.up).comap ((↑) : F → MetricPlane)) =
      levyProkhorovEDist (μ.map (fun z : ℂ => (z - c) / (a : ℂ)))
        (ν.map (fun z : ℂ => (z - c) / (a : ℂ))) := by
  let C := areaCellConfig h hε (S.mult ε ω)
  let e := euclideanCellEquiv h hε
  let : Countable C.cells := Countable.of_equiv ℤ e
  have hpos : ∀ K, 0 < C.holding K := holding_pos_of_forall_exists_adj hcell hadj
  have hQ := S.areaCellConfig_isSRWLaw ω h hε hm x
  have hfinite := S.ae_continuousExitTime_ne_top_all_parentBlock_interior ω h hε hlf hm
    H hH hconn hσ hcell hadj hrec x
  have hfinite' : ∀ᵐ ξ ∂((srwLaw (S.mult ε ω) x).map (fun ξ n => e (ξ n))),
      BouRabeeGwynne.continuousExitTime (planeCoord.symm ⁻¹' interior (ParentBlock.parentBlock c a)) 0
        (C.interpolatedWalk (areaCellRepresentative h hε (S.mult ε ω)) σ ξ) ≠ ∞ := by
    filter_upwards [hfinite] with ξ hξ
    exact hξ c a ha.le
  exact levyProkhorovEDist_walk_brownian_parentFrontier hrec hpos hQ
    (areaCellRepresentative h hε (S.mult ε ω)) hσ c ha hstart hfinite' ρ hρ

end MatedCRT
end
