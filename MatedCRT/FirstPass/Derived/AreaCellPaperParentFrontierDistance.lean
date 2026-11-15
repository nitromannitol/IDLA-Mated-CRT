import MatedCRT.FirstPass.Derived.AreaCellParentInteriorFiniteExit
import MatedCRT.FirstPass.Derived.AreaCellLaw
import MatedCRT.FirstPass.Derived.AreaCellParentPaperExitLaw
import MatedCRT.FirstPass.Derived.AreaCellParentFrontierDistance
import LatticeProb.Prob.WalkBrownianParentFrontier

/-! # Area-cell walk and Brownian parent-frontier distances -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne HarmonicBalls
open MatedCRTHarmonic MatedCRTHarmonic.GMSMain
open LatticeProb LatticeProb.CellConfigWalk LatticeProb.CellConfigInterpolation
open LatticeProb.CellConfigCappedSquare
open scoped NNReal ENNReal

/-- The parent-frontier distance between the area-cell walk and Brownian exit
laws agrees with the distance between their normalized ambient exit laws. -/
theorem MatedCRTEnv.areaCell_paper_parentFrontier_distance
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    {μ : Measure ℂ} (h : IsAreaParametrized μ (S.η ω))
    {ε : ℝ} (hε : 0 < ε)
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
    (hm : IsLocallyFiniteMult (S.mult ε ω))
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf) (0 : ℤ))
    (hH : H.cell = cell ε (S.η ω))
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf).adj.Connected)
    {σ m : ℝ≥0} (hσ : 0 < σ) (hmstep : 0 < m)
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
    let p := areaCellRepresentative h hε (S.mult ε ω)
    let K := euclideanCellEquiv h hε x
    let U := planeCoord.symm ⁻¹' interior (ParentBlock.parentBlock c a)
    let ν := ((stoppedBrownianLaw U ((σ : ℝ) • p K) ρ).map
      BouRabeeGwynne.CurveSpace.endPoint).map planeCoord.symm
    let μ := (srwLaw (S.mult ε ω) x).map (fun ξ =>
      ((σ : ℝ) • interpPathCM (vertexPoint ε (S.η ω)) hmstep.le ξ)
        (pathExitTime (interior (ParentBlock.parentBlock c a))
          ((σ : ℝ) • interpPathCM (vertexPoint ε (S.η ω)) hmstep.le ξ)).toNNReal)
    letI : MetricSpace MetricPlane := normalizedPlaneMetric c a ha.ne'
    let F : Set MetricPlane := MetricPlane.down ⁻¹' frontier (ParentBlock.parentBlock c a)
    levyProkhorovEDist ((μ.map MetricPlane.up).comap ((↑) : F → MetricPlane))
        ((ν.map MetricPlane.up).comap ((↑) : F → MetricPlane)) =
      levyProkhorovEDist (μ.map (fun z : ℂ => (z - c) / (a : ℂ)))
        (ν.map (fun z : ℂ => (z - c) / (a : ℂ))) := by
  let C := areaCellConfig h hε (S.mult ε ω)
  let e := euclideanCellEquiv h hε
  let p := areaCellRepresentative h hε (S.mult ε ω)
  let Q := (srwLaw (S.mult ε ω) x).map (fun ξ n => e (ξ n))
  let U := planeCoord.symm ⁻¹' interior (ParentBlock.parentBlock c a)
  let _ : Countable C.cells := Countable.of_equiv ℤ e
  have hpos : ∀ K, 0 < C.holding K :=
    holding_pos_of_forall_exists_adj hcell hadj
  have hQ := S.areaCellConfig_isSRWLaw ω h hε hm x
  have hU : IsOpen U := isOpen_interior.preimage planeCoord.symm.continuous
  have heval := aemeasurable_interpolatedWalk_exitPosition hrec hpos hQ p σ hU
  have hmap := AEMeasurable.map_map_of_aemeasurable
    (planeCoord.symm.continuous.measurable.aemeasurable) heval
  have hlaw := S.areaCell_parentBlock_holding_exitPosition_law ω h hε hlf hm
    H hH hconn hσ hmstep hcell hrec x c ha.le
  have hd := S.areaCell_parentFrontier_distance ω h hε hlf hm H hH hconn
    hσ hcell hadj hrec x c ha hstart ρ hρ
  have hlaw' : Q.map (fun ξ => planeCoord.symm ((C.interpolatedWalk p σ ξ)
      (BouRabeeGwynne.continuousExitTime U 0 (C.interpolatedWalk p σ ξ)).toNNReal)) =
      (srwLaw (S.mult ε ω) x).map (fun ξ =>
        ((σ : ℝ) • interpPathCM (vertexPoint ε (S.η ω)) hmstep.le ξ)
          (pathExitTime (interior (ParentBlock.parentBlock c a))
            ((σ : ℝ) • interpPathCM (vertexPoint ε (S.η ω)) hmstep.le ξ)).toNNReal) := by
    change Q.map (fun ξ => planeCoord.symm ((C.interpolatedWalk p σ ξ)
      (LatticeProb.continuousExitTime U 0 (C.interpolatedWalk p σ ξ)).toNNReal)) = _
    calc
      _ = (Q.map (fun ξ => (C.interpolatedWalk p σ ξ)
          (LatticeProb.continuousExitTime U 0 (C.interpolatedWalk p σ ξ)).toNNReal)).map
          planeCoord.symm := by
            exact hmap.symm
      _ = _ := hlaw
  dsimp only at hd ⊢
  rw [hlaw'] at hd
  exact hd

end MatedCRT
end
