import MatedCRT.FirstPass.Derived.CouplingPhaseAreaCellWalk
import LatticeProb.Prob.UniformModShift

/-! # Area-cell walks under uniform phase laws -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Filter ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTInput
open scoped NNReal

/-- A uniform phase on one mesh interval gives the conditional shifted cell-walk result. -/
theorem ae_uniformPhaseAreaCellWalk_of_ae_embedding
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
      ∀ᵐ c : ℝ ∂(LatticeProb.uniformIco ε),
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
  apply ae_phaseAreaCellWalk_of_ae_embedding D hγ hε (LatticeProb.uniformIco ε)
  · exact ProbabilityTheory.cond_absolutelyContinuous
  · exact (ProbabilityTheory.ae_cond_mem (μ := volume) measurableSet_Ico).mono
      (fun _ hc => ⟨hc.1, le_of_lt hc.2⟩)
  · exact hemb

end MatedCRT
