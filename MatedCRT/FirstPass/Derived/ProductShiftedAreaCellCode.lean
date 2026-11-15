import MatedCRT.FirstPass.Derived.CouplingShiftedAreaCellGeometry
import MatedCRT.FirstPass.Derived.SelectedShiftedAreaCellCode

/-! # Codes of shifted cells on a product space -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Filter ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTInput
open scoped NNReal

/-- A product-almost-everywhere matching embedding supplies a selected valid
shifted area-cell configuration whose code is almost everywhere measurable. -/
theorem exists_prod_shiftedAreaCellConfig_aemeasurable_code
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 < ε)
    (Q : Measure ℝ) [SFinite Q] (hη : Measurable η) (hbm : Measurable bm)
    (hembed : ∀ᵐ p ∂P.prod Q,
      let w : Path2 := ⟨fun t => bm p.1 (t + p.2),
        (bm p.1).continuous.comp (by fun_prop)⟩
      ∃ (hlf : IsLocallyFinite ε w)
        (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε w hlf) 0),
        H.cell = cell ε (fun t => η p.1 (t + p.2))) :
    ∃ H : Ω × ℝ → CellConfig,
      (∀ᵐ p ∂P.prod Q,
        ∃ h : IsAreaParametrized ((cellModelOfCoupling D hγ).area p.1) (η p.1),
          H p = shiftedAreaCellConfig h hε (p.2 / ε)
            (bmEdgeCount ε (fun t => (bm p.1 (t + p.2)).1)
              (fun t => (bm p.1 (t + p.2)).2)) ∧ (H p).IsCellConfiguration) ∧
      AEMeasurable (fun p => (H p).code) (P.prod Q) := by
  have hgood := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := Q)).ae
    (ae_shiftedAreaCellConfig_of_coupling D hγ hε)
  have hvalid : ∀ᵐ p ∂P.prod Q,
      ∃ h : IsAreaParametrized ((cellModelOfCoupling D hγ).area p.1) (η p.1),
        (shiftedAreaCellConfig h hε (p.2 / ε)
          (bmEdgeCount ε (fun t => (bm p.1 (t + ε * (p.2 / ε))).1)
            (fun t => (bm p.1 (t + ε * (p.2 / ε))).2))).IsCellConfiguration := by
    filter_upwards [hgood, hembed] with p hp he
    obtain ⟨h, hh⟩ := hp
    obtain ⟨hlf, H, hH⟩ := he
    have hc := (hh p.2 hlf H hH).1
    refine ⟨h, ?_⟩
    simpa only [ContinuousMap.coe_mk, mul_div_cancel₀ _ (ne_of_gt hε)] using hc
  obtain ⟨H, hH, hcode⟩ := exists_shiftedAreaCellConfig_aemeasurable_code
    (P.prod Q) hε (η ∘ Prod.fst) (bm ∘ Prod.fst) (fun p => p.2 / ε)
    (fun p => (cellModelOfCoupling D hγ).area p.1)
    (hη.comp measurable_fst) (hbm.comp measurable_fst)
    (measurable_snd.div_const ε) hvalid
  refine ⟨H, ?_, hcode⟩
  filter_upwards [hH] with p hp
  simpa only [Function.comp_apply, mul_div_cancel₀ _ (ne_of_gt hε)] using hp

end MatedCRT
