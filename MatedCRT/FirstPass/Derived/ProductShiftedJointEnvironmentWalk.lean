import MatedCRT.FirstPass.Derived.ProductShiftedGeneralCodeLaw
import LatticeProb.Probability.MapRestrictSubtype

/-! # Joint general environment and selected walk laws -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Filter Topology ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTInput
open scoped NNReal

/-- A matching shifted embedding gives a measurable general environment jointly
with the selected walk law, preserving their raw-code joint law. -/
theorem exists_prod_shiftedAreaCellConfig_jointEnvironment_selectedWalkLaw
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 < ε) (m : ℝ≥0)
    (Q : Measure ℝ) [IsProbabilityMeasure Q] (x : Ω × ℝ → ℂ)
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
      (Z : Ω × ℝ → ReflectedGMS.Code.RawCode × Measure C(ℝ≥0, ℂ))
      (E : Ω × ℝ → ReflectedGMS.Code.EnvGeneral),
      Measurable Z ∧ Measurable E ∧
      (P.prod Q).map (fun p => ((E p).val, (Z p).2)) = (P.prod Q).map Z ∧
      ∀ᵐ p ∂P.prod Q,
        (∃ h : IsAreaParametrized ((cellModelOfCoupling D hγ).area p.1) (η p.1),
          H p = shiftedAreaCellConfig h hε (p.2 / ε)
            (bmEdgeCount ε (fun t => (bm p.1 (t + p.2)).1)
              (fun t => (bm p.1 (t + p.2)).2)) ∧
          (H p).IsCellConfiguration ∧ (H p).LineConnected) ∧
        Z p = ((H p).code, shiftedSelectedWalkLaw ε m p.2 (x p) (η p.1) (bm p.1)) ∧
        (Z p).1 ∈ goodCodes ∧ (E p).val = (Z p).1 := by
  let : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨H, Z, hZ, _, hmatch⟩ :=
    exists_prod_shiftedAreaCellConfig_generalCodeLaw_selectedWalkLaw
      D hγ hε m Q x hη hbm hx hcurve hembed
  have hvalid : ∀ᵐ p ∂P.prod Q, ReflectedGMS.Code.ValidGeneral (Z p).1 :=
    hmatch.mono fun _ hp => validGeneral_of_mem_goodCodes hp.2.2
  obtain ⟨p, hp⟩ := hvalid.exists
  have hne : {r : ReflectedGMS.Code.RawCode | ReflectedGMS.Code.ValidGeneral r}.Nonempty :=
    ⟨(Z p).1, hp⟩
  obtain ⟨E, hE, hEZ⟩ :=
    LatticeProb.exists_measurable_subtype_ae_eq hZ.fst hne hvalid
  refine ⟨H, Z, E, hZ, hE, ?_, ?_⟩
  · apply Measure.map_congr
    filter_upwards [hEZ] with p hp
    exact Prod.ext hp rfl
  · filter_upwards [hmatch, hEZ] with p hp he
    exact ⟨hp.1, hp.2.1, hp.2.2, he⟩

end MatedCRT
