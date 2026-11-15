import MatedCRT.FirstPass.Derived.ProductShiftedGoodCodeWalk

/-! # General environment laws for shifted cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Filter Topology ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTInput
open scoped NNReal

/-- Matching shifted embeddings yield a raw-code law supported on general
environments, jointly with the selected walk law and matching configuration. -/
theorem exists_prod_shiftedAreaCellConfig_generalCodeLaw_selectedWalkLaw
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
    ∃ (H : Ω × ℝ → CellConfig)
      (Z : Ω × ℝ → ReflectedGMS.Code.RawCode × Measure C(ℝ≥0, ℂ)),
      Measurable Z ∧
      ReflectedGMS.GeneralLaws.SupportedOnValidGeneral
        ((P.prod Q).map (fun p => (Z p).1)) ∧
      ∀ᵐ p ∂P.prod Q,
        (∃ h : IsAreaParametrized ((cellModelOfCoupling D hγ).area p.1) (η p.1),
          H p = shiftedAreaCellConfig h hε (p.2 / ε)
            (bmEdgeCount ε (fun t => (bm p.1 (t + p.2)).1)
              (fun t => (bm p.1 (t + p.2)).2)) ∧
          (H p).IsCellConfiguration ∧ (H p).LineConnected) ∧
        Z p = ((H p).code, shiftedSelectedWalkLaw ε m p.2 (x p) (η p.1) (bm p.1)) ∧
        (Z p).1 ∈ goodCodes := by
  obtain ⟨H, Z, hZ, hmatch⟩ :=
    exists_prod_shiftedAreaCellConfig_goodCode_selectedWalkLaw
      D hγ hε m Q x hη hbm hx hcurve hembed
  refine ⟨H, Z, hZ, ?_, hmatch⟩
  have hgood : ∀ᵐ r ∂(P.prod Q).map (fun p => (Z p).1), r ∈ goodCodes :=
    (ae_map_iff hZ.fst.aemeasurable measurableSet_goodCodes).2
      (hmatch.mono fun _ hp => hp.2.2)
  exact hgood.mono fun _ hr => validGeneral_of_mem_goodCodes hr

end MatedCRT
