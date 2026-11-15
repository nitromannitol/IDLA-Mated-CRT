import MatedCRT.FirstPass.Derived.CouplingPhaseAreaCellWalk
import MatedCRT.FirstPass.Derived.CouplingAreaParametrization

/-! # Area-cell walks at countably many meshes -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Filter ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTInput
open scoped NNReal

/-- For countably many meshes, one area witness supports the conditional walk
laws under each fixed absolutely continuous phase law. -/
theorem ae_countable_phaseAreaCellWalk_of_ae_embedding
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {ι : Type} [Countable ι] (ε : ι → ℝ) (hε : ∀ i, 0 < ε i)
    (Q : ι → Measure ℝ) (hQ : ∀ i, Q i ≪ volume)
    (hQmem : ∀ i, ∀ᵐ c ∂Q i, c ∈ Icc 0 (ε i))
    (hemb : ∀ i, ∀ᵐ ω ∂P, ∀ᵐ c : ℝ ∂volume, 0 ≤ c → c ≤ ε i →
      ∃ (hlf : IsLocallyFinite (ε i)
          ⟨fun t => bm ω (t + c), (bm ω).continuous.comp (by fun_prop)⟩)
        (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph (ε i)
          ⟨fun t => bm ω (t + c), (bm ω).continuous.comp (by fun_prop)⟩ hlf) 0),
        H.cell = cell (ε i) (fun t => η ω (t + c))) :
    ∀ᵐ ω ∂P, ∃ h : IsAreaParametrized ((cellModelOfCoupling D hγ).area ω) (η ω),
      ∀ i, ∀ᵐ c : ℝ ∂Q i,
        ∃ (hlf : IsLocallyFinite (ε i)
            ⟨fun t => bm ω (t + c), (bm ω).continuous.comp (by fun_prop)⟩)
          (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph (ε i)
            ⟨fun t => bm ω (t + c), (bm ω).continuous.comp (by fun_prop)⟩ hlf) 0),
          H.cell = cell (ε i) (fun t => η ω (t + c)) ∧
          let w : Path2 := ⟨fun t => bm ω (t + c), (bm ω).continuous.comp (by fun_prop)⟩
          let m := bmEdgeCount (ε i) (fun t => (w t).1) (fun t => (w t).2)
          let C := shiftedAreaCellConfig h (hε i) (c / ε i) m
          C.IsCellConfiguration ∧ C.LineConnected ∧
            ∀ a : ℤ, C.IsSRWLaw (shiftedEuclideanCellEquiv h (hε i) (c / ε i) a)
              ((srwLaw m a).map (fun p n => shiftedEuclideanCellEquiv h (hε i) (c / ε i) (p n))) := by
  filter_upwards [ae_isAreaParametrized_of_coupling D hγ,
    ae_all_iff.2 (fun i => ae_phaseAreaCellWalk_of_ae_embedding D hγ
      (hε i) (Q i) (hQ i) (hQmem i) (hemb i))] with ω harea hwalk
  refine ⟨harea, ?_⟩
  intro i
  obtain ⟨h, hh⟩ := hwalk i
  exact hh

end MatedCRT
