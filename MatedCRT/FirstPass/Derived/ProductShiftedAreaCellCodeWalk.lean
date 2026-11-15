import MatedCRT.FirstPass.Derived.ProductShiftedAreaCellCode
import MatedCRT.FirstPass.Derived.JointShiftedAreaCellCodeWalk

/-! # Joint codes and selected walks for shifted cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Filter Topology ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTInput
open scoped NNReal

/-- Matching shifted embeddings yield a selected valid cell configuration whose
code and selected walk law are jointly almost everywhere measurable. -/
theorem exists_prod_shiftedAreaCellConfig_aemeasurable_code_selectedWalkLaw
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 < ε) (m : ℝ≥0)
    (Q : Measure ℝ) [SFinite Q] (x : Ω × ℝ → ℂ)
    (hη : Measurable η) (hbm : Measurable bm) (hx : Measurable x)
    (hcurve : ∀ᵐ ω ∂P, Tendsto (η ω) (cocompact ℝ) (cocompact ℂ) ∧
      Function.Surjective (η ω))
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
      AEMeasurable (fun p => ((H p).code,
        shiftedSelectedWalkLaw ε m p.2 (x p) (η p.1) (bm p.1))) (P.prod Q) := by
  obtain ⟨H, hH, _⟩ :=
    exists_prod_shiftedAreaCellConfig_aemeasurable_code D hγ hε Q hη hbm hembed
  refine ⟨H, hH, ?_⟩
  have hc := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := Q)).ae hcurve
  have hH' : ∀ᵐ p ∂P.prod Q,
      ∃ h : IsAreaParametrized ((cellModelOfCoupling D hγ).area p.1) (η p.1),
        H p = shiftedAreaCellConfig h hε (p.2 / ε)
          (bmEdgeCount ε (fun t => (bm p.1 (t + ε * (p.2 / ε))).1)
            (fun t => (bm p.1 (t + ε * (p.2 / ε))).2)) ∧ (H p).IsCellConfiguration := by
    simpa only [mul_div_cancel₀ _ (ne_of_gt hε)] using hH
  have hj := aemeasurable_shiftedAreaCellConfig_code_selectedWalkLaw
    (P.prod Q) hε m (η ∘ Prod.fst) (bm ∘ Prod.fst) (fun p => p.2 / ε) x
    (fun p => (cellModelOfCoupling D hγ).area p.1) H
    (hη.comp measurable_fst) (hbm.comp measurable_fst) (measurable_snd.div_const ε)
    hx hc hH'
  simpa only [Function.comp_apply, mul_div_cancel₀ _ (ne_of_gt hε)] using hj

end MatedCRT
