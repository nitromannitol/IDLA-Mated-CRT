import MatedCRT.FirstPass.Derived.CouplingUniformPhaseAreaCellWalk
import MatedCRT.FirstPass.Derived.CouplingCountablePhaseAreaCellWalk
import LatticeProb.LQG.CouplingShiftedCellEmbedding

/-! # Shifted area-cell walks in a mating-of-trees coupling -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Filter ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTInput
open scoped NNReal

/-- For almost every sample, an area witness gives the shifted walk laws at every integer start for almost every in-mesh phase. -/
theorem ae_shiftedAreaCellWalk_ae_of_coupling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 < ε) :
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
  exact ae_shiftedAreaCellWalk_of_ae_embedding D hγ hε (ae_shifted_cellularEmbedding_of_coupling D hε)

/-- The same shifted walk laws hold for any fixed supported phase law absolutely continuous with respect to volume. -/
theorem ae_phaseAreaCellWalk_of_coupling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 < ε)
    (Q : Measure ℝ) (hQ : Q ≪ volume) (hQmem : ∀ᵐ c ∂Q, c ∈ Icc 0 ε) :
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
  exact ae_phaseAreaCellWalk_of_ae_embedding D hγ hε Q hQ hQmem (ae_shifted_cellularEmbedding_of_coupling D hε)

/-- The same shifted walk laws hold for a uniform phase on the mesh interval. -/
theorem ae_uniformPhaseAreaCellWalk_of_coupling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 < ε) :
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
  exact ae_uniformPhaseAreaCellWalk_of_ae_embedding D hγ hε (ae_shifted_cellularEmbedding_of_coupling D hε)

/-- For countably many positive meshes, one area witness gives the shifted walk laws at every start under each fixed supported absolutely continuous phase law. -/
theorem ae_countable_phaseAreaCellWalk_of_coupling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {ι : Type} [Countable ι] (ε : ι → ℝ) (hε : ∀ i, 0 < ε i)
    (Q : ι → Measure ℝ) (hQ : ∀ i, Q i ≪ volume)
    (hQmem : ∀ i, ∀ᵐ c ∂Q i, c ∈ Icc 0 (ε i)) :
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
  exact ae_countable_phaseAreaCellWalk_of_ae_embedding D hγ ε hε Q hQ hQmem (fun i => ae_shifted_cellularEmbedding_of_coupling D (hε i))

end MatedCRT
