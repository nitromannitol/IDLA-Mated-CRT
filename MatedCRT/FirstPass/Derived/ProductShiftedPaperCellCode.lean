import MatedCRT.FirstPass.Derived.ProductShiftedAreaCellCode
import MatedCRT.FirstPass.Derived.ShiftedPaperMultiplicity

/-! # Product-space shifted cell codes with geometric multiplicities -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTInput
open scoped NNReal

/-- If the translated Brownian edge counts agree with the geometric cell
multiplicities, a matching embedding gives a valid configuration with an
almost-everywhere measurable code on the same product space. -/
theorem exists_prod_shiftedAreaCellConfig_aemeasurable_code_of_cellMult
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
        H.cell = cell ε (fun t => η p.1 (t + p.2)))
    (hmatch : ∀ᵐ p ∂P.prod Q,
      bmEdgeCount ε (fun t => (bm p.1 (t + p.2)).1)
          (fun t => (bm p.1 (t + p.2)).2) =
        cellMult ε (fun t => η p.1 (t + p.2))) :
    ∃ H : Ω × ℝ → CellConfig,
      (∀ᵐ p ∂P.prod Q,
        ∃ h : IsAreaParametrized ((cellModelOfCoupling D hγ).area p.1) (η p.1),
          H p = shiftedAreaCellConfig h hε (p.2 / ε)
            (cellMult ε (fun t => η p.1 (t + p.2))) ∧ (H p).IsCellConfiguration) ∧
      AEMeasurable (fun p => (H p).code) (P.prod Q) := by
  obtain ⟨H, hH, hcode⟩ :=
    exists_prod_shiftedAreaCellConfig_aemeasurable_code D hγ hε Q hη hbm hembed
  refine ⟨H, ?_, hcode⟩
  filter_upwards [hH, hmatch] with p hp hm
  obtain ⟨h, heq, hv⟩ := hp
  exact ⟨h, by rw [← hm]; exact heq, hv⟩

end MatedCRT
