import MatedCRT.FirstPass.Derived.AreaCellParentInteriorFiniteExit

/-! # Initial points and finite parent-block exits of area-cell walks -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.GMSMain
open LatticeProb.ParentBlock LatticeProb.CellConfigInterpolation
open scoped NNReal ENNReal

/-- The interpolated walk starts at the scaled embedded vertex and exits all
parent-block interiors in finite time, on one full-measure event. -/
theorem MatedCRTEnv.ae_areaCell_start_and_parentBlock_interior_exit
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
    (hrec : (areaCellConfig h hε (S.mult ε ω)).Recurrent) (x : ℤ) :
    ∀ᵐ ξ ∂((srwLaw (S.mult ε ω) x).map (fun ξ n => euclideanCellEquiv h hε (ξ n))),
      (areaCellConfig h hε (S.mult ε ω)).interpolatedWalk
          (areaCellRepresentative h hε (S.mult ε ω)) σ ξ 0 =
        (σ : ℝ) • Complex.orthonormalBasisOneI.repr (vertexPoint ε (S.η ω) x) ∧
      ∀ (c : ℂ) (s : ℝ), 0 ≤ s →
        BouRabeeGwynne.continuousExitTime
          (Complex.orthonormalBasisOneI.repr.symm ⁻¹' interior (parentBlock c s)) 0
          ((areaCellConfig h hε (S.mult ε ω)).interpolatedWalk
            (areaCellRepresentative h hε (S.mult ε ω)) σ ξ) ≠ ∞ := by
  let C := areaCellConfig h hε (S.mult ε ω)
  let e := euclideanCellEquiv h hε
  let Q := (srwLaw (S.mult ε ω) x).map (fun ξ n => e (ξ n))
  let : Countable C.cells := Countable.of_equiv ℤ e
  have hQ : C.IsSRWLaw (e x) Q := S.areaCellConfig_isSRWLaw ω h hε hm x
  have hpos : ∀ K, 0 < C.holding K :=
    LatticeProb.CellConfigWalk.holding_pos_of_forall_exists_adj hcell hadj
  have hzero : ∀ᵐ ξ ∂Q, ξ 0 = e x := by
    let e' : ℤ ≃ᵐ C.cells :=
      { toEquiv := e
        measurable_toFun := measurable_of_countable _
        measurable_invFun := measurable_of_countable _ }
    let E : (ℕ → ℤ) ≃ᵐ (ℕ → C.cells) :=
      MeasurableEquiv.piCongrRight (fun _ => e')
    change ∀ᵐ ξ ∂(srwLaw (S.mult ε ω) x).map E, _
    apply E.measurableEmbedding.ae_map_iff.mpr
    filter_upwards [srwLaw_ae_start (S.mult ε ω) x] with ξ hξ
    exact congrArg e hξ
  filter_upwards [hzero,
    LatticeProb.CellConfigWalk.ae_jumpTimesUnbounded_of_recurrent hrec hpos hQ,
    S.ae_continuousExitTime_ne_top_all_parentBlock_interior ω h hε hlf hm
      H hH hconn hσ hcell hadj hrec x] with ξ hξ hunb hexit
  refine ⟨?_, hexit⟩
  have ht : (⟨(σ : ℝ) ^ 2 * C.jumpTime ξ 0,
      mul_nonneg (sq_nonneg _) (C.jumpTime_nonneg hpos 0)⟩ : ℝ≥0) = 0 := by
    apply Subtype.ext
    simp [CellConfig.jumpTime]
  have hk := interpolatedWalk_at_jumpTime C
    (areaCellRepresentative h hε (S.mult ε ω)) ξ hpos hunb 0 hσ
  rw [ht, hξ, areaCellRepresentative_equiv] at hk
  exact hk

end MatedCRT
end
