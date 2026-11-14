import MatedCRT.FirstPass.Derived.AreaCellEnvironmentFiniteExit
import MatedCRT.FirstPass.Derived.AreaCellShiftedFrontierHit
import MatedCRT.FirstPass.Derived.SrwStrictAdjacency
import MatedCRT.FirstPass.Derived.AreaCellGraph

/-! # Good paths for exit-law comparisons of area-cell walks -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.Markov MatedCRTHarmonic.GMSMain
open scoped NNReal ENNReal

/-- A recurrent area-cell walk started in a bounded open set reaches its
frontier, has an unbounded clock, and exits every bounded outer set. -/
theorem MatedCRTEnv.ae_areaCell_exit_good_paths
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
    (V W : Set ReflectedGMS.Plane) (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hWb : Bornology.IsBounded W)
    (hstart : (((euclideanCellEquiv h hε x).1 : Set ReflectedGMS.Plane) ∩ V).Nonempty) :
    ∀ᵐ ξ ∂((srwLaw (S.mult ε ω) x).map (fun ξ n => euclideanCellEquiv h hε (ξ n))),
      (((ξ 0).1 : Set ReflectedGMS.Plane) ∩ V).Nonempty ∧
      (∀ n, (areaCellConfig h hε (S.mult ε ω)).Adj (ξ n) (ξ (n + 1))) ∧
      (areaCellConfig h hε (S.mult ε ω)).JumpTimesUnbounded ξ ∧
      hitTime {K : (areaCellConfig h hε (S.mult ε ω)).cells |
        ((K.1 : Set ReflectedGMS.Plane) ∩ frontier V).Nonempty} ξ ≠ ⊤ ∧
      BouRabeeGwynne.continuousExitTime W 0
        ((areaCellConfig h hε (S.mult ε ω)).interpolatedWalk
          (areaCellRepresentative h hε (S.mult ε ω)) σ ξ) ≠ ∞ := by
  let C := areaCellConfig h hε (S.mult ε ω)
  let e := euclideanCellEquiv h hε
  let Q := (srwLaw (S.mult ε ω) x).map (fun ξ n => e (ξ n))
  let : Countable C.cells := Countable.of_equiv ℤ e
  have hQ : C.IsSRWLaw (e x) Q := S.areaCellConfig_isSRWLaw ω h hε hm x
  have hpos : ∀ K, 0 < C.holding K :=
    LatticeProb.CellConfigWalk.holding_pos_of_forall_exists_adj hcell hadj
  have hunb : ∀ᵐ ξ ∂Q, C.JumpTimesUnbounded ξ :=
    LatticeProb.CellConfigWalk.ae_jumpTimesUnbounded_of_recurrent hrec hpos hQ
  have hsteps : ∀ᵐ ξ ∂Q, ξ 0 = e x ∧ ∀ n, C.Adj (ξ n) (ξ (n + 1)) := by
    let e' : ℤ ≃ᵐ C.cells :=
      { toEquiv := e
        measurable_toFun := measurable_of_countable _
        measurable_invFun := measurable_of_countable _ }
    let E : (ℕ → ℤ) ≃ᵐ (ℕ → C.cells) :=
      MeasurableEquiv.piCongrRight (fun _ => e')
    change ∀ᵐ ξ ∂(srwLaw (S.mult ε ω) x).map E, _
    apply E.measurableEmbedding.ae_map_iff.mpr
    filter_upwards [srwLaw_ae_start (S.mult ε ω) x,
      srwLaw_ae_adj (S.mult ε ω) hm (S.mult_mdeg_pos hε.le ω hm)
        (S.mult_self ε ω) x] with ξ hzero hstep
    refine ⟨?_, fun n => ?_⟩
    · change e (ξ 0) = e x
      exact congrArg e hzero
    · exact ((areaCellConfig_graph_adj_iff h hε _ (S.mult_symm ε ω) _ _).2 (hstep n)).2.1
  have hhit := ae_hitTime_frontier_ne_top_all_bounded_open_all_shifts_areaCell
    h hε (S.mult ε ω) hlf H hH hconn x
  have hexit := S.ae_continuousExitTime_ne_top_all_bounded_areaCell ω h hε hlf hm
    H hH hconn hσ hcell hadj hrec x
  filter_upwards [hsteps, hunb, hhit, hexit] with ξ hs hu hh he
  have hsV : (((ξ 0).1 : Set ReflectedGMS.Plane) ∩ V).Nonempty := by
    rw [hs.1]
    exact hstart
  exact ⟨hsV, hs.2, hu, by simpa using hh V hVb hV 0 hsV, he W hWb⟩

end MatedCRT
end
