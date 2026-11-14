import MatedCRT.FirstPass.Derived.AreaCellExitGoodPaths
import MatedCRT.FirstPass.Derived.AreaCellSeparationProbability
import MatedCRT.FirstPass.Derived.AreaCellUnitBallBoundary
import LatticeProb.Walk.CellConfigFirstHitExitLaw

/-! # Exit-law comparison for area-parametrized cells -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Metric Set ReflectedGMS ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.Markov MatedCRTHarmonic.HarmonicInfinity
open scoped NNReal ENNReal

/-- A high probability of separating an inner set before reaching a frontier
controls the distance between the outer exit laws of two area-cell walks. -/
theorem MatedCRTEnv.levyProkhorovEDist_areaCell_exit_le
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
    (hrec : (areaCellConfig h hε (S.mult ε ω)).Recurrent)
    (ρ R d r : ℝ) (hρ : ρ < 1) (hρR : ρ ≤ R)
    (hd : ∀ k, (cell ε (S.η ω) k ∩ ball 0 1).Nonempty →
      diam (cell ε (S.η ω) k) ≤ d) (hgap : d < R - ρ)
    (W : Set Plane) (hW : IsOpen W) (hWb : Bornology.IsBounded W)
    (hscale : ∀ z ∈ ball (Complex.orthonormalBasisOneI.repr 0) R, (σ : ℝ) • z ∈ W)
    (x y : ℤ)
    (hxstart : (((euclideanCellEquiv h hε x).1 : Set Plane) ∩
      ball (Complex.orthonormalBasisOneI.repr 0) ρ).Nonempty)
    (hystart : (((euclideanCellEquiv h hε y).1 : Set Plane) ∩
      ball (Complex.orthonormalBasisOneI.repr 0) ρ).Nonempty)
    (hyB : (((euclideanCellEquiv h hε y).1 : Set Plane) ∩
      closedBall (Complex.orthonormalBasisOneI.repr 0) r).Nonempty)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hD : 1 - δ ≤ (srwLaw (S.mult ε ω) x
      {ξ | walkSetDisconnectsBeforeHit (S.mult ε ω)
        (cellVertices ε (S.η ω) (closedBall 0 r))
        (cellVertices ε (S.η ω) (frontier (ball 0 ρ))) ξ}).toReal) :
    levyProkhorovEDist
      (((srwLaw (S.mult ε ω) x).map (fun ξ n => euclideanCellEquiv h hε (ξ n))).map
        (fun ξ => ((areaCellConfig h hε (S.mult ε ω)).interpolatedWalk
          (areaCellRepresentative h hε (S.mult ε ω)) σ ξ)
          (BouRabeeGwynne.continuousExitTime W 0
            ((areaCellConfig h hε (S.mult ε ω)).interpolatedWalk
              (areaCellRepresentative h hε (S.mult ε ω)) σ ξ)).toNNReal))
      (((srwLaw (S.mult ε ω) y).map (fun ξ n => euclideanCellEquiv h hε (ξ n))).map
        (fun ξ => ((areaCellConfig h hε (S.mult ε ω)).interpolatedWalk
          (areaCellRepresentative h hε (S.mult ε ω)) σ ξ)
          (BouRabeeGwynne.continuousExitTime W 0
            ((areaCellConfig h hε (S.mult ε ω)).interpolatedWalk
              (areaCellRepresentative h hε (S.mult ε ω)) σ ξ)).toNNReal)) ≤ ENNReal.ofReal δ := by
  let C := areaCellConfig h hε (S.mult ε ω)
  let e := euclideanCellEquiv h hε
  let Qx := (srwLaw (S.mult ε ω) x).map (fun ξ n => e (ξ n))
  let Qy := (srwLaw (S.mult ε ω) y).map (fun ξ n => e (ξ n))
  let V := ball (Complex.orthonormalBasisOneI.repr 0) ρ
  let U := ball (Complex.orthonormalBasisOneI.repr 0) R
  let I : Set C.cells := {K | ((K.1 : Set Plane) ∩ frontier V).Nonempty}
  let B : Set C.cells := {K | ((K.1 : Set Plane) ∩
    closedBall (Complex.orthonormalBasisOneI.repr 0) r).Nonempty}
  let : Countable C.cells := Countable.of_equiv ℤ e
  have hQx : C.IsSRWLaw (e x) Qx := S.areaCellConfig_isSRWLaw ω h hε hm x
  have hQy : C.IsSRWLaw (e y) Qy := S.areaCellConfig_isSRWLaw ω h hε hm y
  let instQx : IsProbabilityMeasure Qx := hQx.1
  let instQy : IsProbabilityMeasure Qy := hQy.1
  have hgx := S.ae_areaCell_exit_good_paths ω h hε hlf hm H hH hconn hσ hcell hadj hrec x
    V W isOpen_ball (isBounded_ball) hWb hxstart
  have hgy := S.ae_areaCell_exit_good_paths ω h hε hlf hm H hH hconn hσ hcell hadj hrec y
    V W isOpen_ball (isBounded_ball) hWb hystart
  have hx : Qx {ξ | hitTime I ξ ≠ ⊤} = 1 := by
    apply (mem_ae_iff_prob_eq_one (μ := Qx) (measurableSet_hitTime_eq_top (A := I)
      MeasurableSet.of_discrete).compl).1
    filter_upwards [hgx] with ξ hξ
    exact hξ.2.2.2.1
  have hy : Qy {ξ | hitTime I ξ ≠ ⊤} = 1 := by
    apply (mem_ae_iff_prob_eq_one (μ := Qy) (measurableSet_hitTime_eq_top (A := I)
      MeasurableSet.of_discrete).compl).1
    filter_upwards [hgy] with ξ hξ
    exact hξ.2.2.2.1
  have hsep : 1 - δ ≤ (Qx {ξ | GraphSeparates C.graph (traceBefore id I ξ) B I}).toReal := by
    rw [show Qx {ξ | GraphSeparates C.graph (traceBefore id I ξ) B I} =
      srwLaw (S.mult ε ω) x {ξ | walkSetDisconnectsBeforeHit (S.mult ε ω)
        (cellVertices ε (S.η ω) (closedBall 0 r))
        (cellVertices ε (S.η ω) (frontier (ball 0 ρ))) ξ} from
      measure_areaCell_separation_eq h hε (S.mult ε ω) (S.mult_symm ε ω) 0 r ρ _]
    exact hD
  have hVU : V ⊆ U := Metric.ball_subset_ball hρR
  exact LatticeProb.CellConfigSRW.levyProkhorovEDist_exitPosition_le_of_set_separation
    C hcell hadj hrec isOpen_ball hVU (convex_ball _ _) hW
    (areaCellRepresentative h hε (S.mult ε ω))
    (areaCellRepresentative_mem h hε (S.mult ε ω))
    (areaCellConfig_subset_outer_ball_of_unit_ball_diam h hε _ ρ R d hρ hd hgap)
    hσ hscale B hQx hQy hyB hδ hsep hx hy hgx hgy

end MatedCRT
end
