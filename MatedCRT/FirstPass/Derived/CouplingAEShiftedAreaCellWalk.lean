import MatedCRT.FirstPass.Derived.CouplingShiftedAreaCellWalk

/-! # Almost-everywhere shifted cell walks in a mating-of-trees coupling -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Filter ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTInput
open scoped NNReal

/-- An almost-everywhere family of matching embeddings gives shifted area-cell
configurations and their Brownian-edge walk laws for every integer start. -/
theorem ae_shiftedAreaCellWalk_of_ae_embedding
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 < ε)
    (hemb : ∀ᵐ ω ∂P, ∀ᵐ c : ℝ ∂volume, 0 ≤ c → c ≤ ε →
      ∃ (hlf : IsLocallyFinite ε
          ⟨fun t => bm ω (t + c), (bm ω).continuous.comp (by fun_prop)⟩)
        (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε
          ⟨fun t => bm ω (t + c), (bm ω).continuous.comp (by fun_prop)⟩ hlf) 0),
        H.cell = cell ε (fun t => η ω (t + c))) :
    ∀ᵐ ω ∂P, ∃ h : IsAreaParametrized ((cellModelOfCoupling D hγ).area ω) (η ω),
      ∀ᵐ c : ℝ ∂volume, 0 ≤ c → c ≤ ε →
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
  filter_upwards [ae_shiftedAreaCellWalk_of_coupling D hγ hε, hemb] with ω hw he
  obtain ⟨h, hw⟩ := hw
  refine ⟨h, ?_⟩
  filter_upwards [he] with c hc
  intro hc0 hcε
  obtain ⟨hlf, H, hH⟩ := hc hc0 hcε
  exact ⟨hlf, H, hH, hw c hlf H hH⟩

end MatedCRT
