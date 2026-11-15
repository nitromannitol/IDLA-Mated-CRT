import MatedCRT.FirstPass.Derived.CouplingAEShiftedAreaCellWalk

/-! # Area-cell walks under absolutely continuous phase laws -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Filter ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTInput
open scoped NNReal

/-- A phase law supported on one mesh interval and absolutely continuous with
respect to Lebesgue measure inherits the conditional shifted cell-walk result. -/
theorem ae_phaseAreaCellWalk_of_ae_embedding
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 < ε)
    (Q : Measure ℝ) (hQ : Q ≪ volume) (hQmem : ∀ᵐ c ∂Q, c ∈ Icc 0 ε)
    (hemb : ∀ᵐ ω ∂P, ∀ᵐ c : ℝ ∂volume, 0 ≤ c → c ≤ ε →
      ∃ (hlf : IsLocallyFinite ε
          ⟨fun t => bm ω (t + c), (bm ω).continuous.comp (by fun_prop)⟩)
        (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε
          ⟨fun t => bm ω (t + c), (bm ω).continuous.comp (by fun_prop)⟩ hlf) 0),
        H.cell = cell ε (fun t => η ω (t + c))) :
    ∀ᵐ ω ∂P, ∃ h : IsAreaParametrized ((cellModelOfCoupling D hγ).area ω) (η ω),
      ∀ᵐ c : ℝ ∂Q,
        ∃ (hlf : IsLocallyFinite ε
            ⟨fun t => bm ω (t + c), (bm ω).continuous.comp (by fun_prop)⟩)
          (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε
            ⟨fun t => bm ω (t + c), (bm ω).continuous.comp (by fun_prop)⟩ hlf) 0),
          H.cell = cell ε (fun t => η ω (t + c)) ∧
          let w : Path2 := ⟨fun t => bm ω (t + c), (bm ω).continuous.comp (by fun_prop)⟩
          let m := bmEdgeCount ε (fun t => (w t).1) (fun t => (w t).2)
          let C := shiftedAreaCellConfig h hε (c / ε) m
          C.IsCellConfiguration ∧ C.LineConnected ∧
            ∀ a : ℤ, C.IsSRWLaw (shiftedEuclideanCellEquiv h hε (c / ε) a)
              ((srwLaw m a).map (fun p n => shiftedEuclideanCellEquiv h hε (c / ε) (p n))) := by
  filter_upwards [ae_shiftedAreaCellWalk_of_ae_embedding D hγ hε hemb] with ω hω
  obtain ⟨h, hphase⟩ := hω
  refine ⟨h, ?_⟩
  filter_upwards [hQ.ae_le hphase, hQmem] with c hc hmem
  exact hc hmem.1 hmem.2

end MatedCRT
