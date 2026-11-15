import MatedCRT.FirstPass.Derived.CouplingEmbeddedAreaCellWalk

/-! # Shifted area-cell walks in valid environments -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTInput
open scoped NNReal

/-- For a countable family of positive meshes and fixed supported absolutely
continuous phase laws, a valid environment almost surely has shifted cell
configurations and their walk laws for almost every phase at every start. -/
theorem MatedCRTEnv.IsValid.ae_countable_phaseAreaCellWalk
    {Ω ι : Type} [MeasurableSpace Ω] [Countable ι]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hS : S.IsValid 𝒮 γ) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (ε : ι → ℝ) (hε : ∀ i, 0 < ε i)
    (Q : ι → Measure ℝ) (hQ : ∀ i, Q i ≪ volume)
    (hQmem : ∀ i, ∀ᵐ c ∂Q i, c ∈ Icc 0 (ε i)) :
    ∀ᵐ ω ∂S.P, ∃ h : IsAreaParametrized (S.μ ω) (S.η ω),
      ∀ i, ∀ᵐ c : ℝ ∂Q i,
        ∃ (hlf : IsLocallyFinite (ε i)
            ⟨fun t => S.bm ω (t + c), (S.bm ω).continuous.comp (by fun_prop)⟩)
          (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph (ε i)
            ⟨fun t => S.bm ω (t + c), (S.bm ω).continuous.comp (by fun_prop)⟩ hlf) 0),
          H.cell = cell (ε i) (fun t => S.η ω (t + c)) ∧
          let w : Path2 := ⟨fun t => S.bm ω (t + c), (S.bm ω).continuous.comp (by fun_prop)⟩
          let m := bmEdgeCount (ε i) (fun t => (w t).1) (fun t => (w t).2)
          let C := shiftedAreaCellConfig h (hε i) (c / ε i) m
          C.IsCellConfiguration ∧ C.LineConnected ∧
            ∀ a : ℤ, C.IsSRWLaw (shiftedEuclideanCellEquiv h (hε i) (c / ε i) a)
              ((srwLaw m a).map (fun p n => shiftedEuclideanCellEquiv h (hε i) (c / ε i) (p n))) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, ηc, _, hC, hη⟩ := hS.matingOfTrees
  filter_upwards [hS.isAreaParametrized, hη,
    ae_countable_phaseAreaCellWalk_of_coupling hC hγ ε hε Q hQ hQmem] with ω harea hηω hw
  obtain ⟨hc, hw⟩ := hw
  rw [← hηω.1] at harea ⊢
  exact ⟨harea, hw⟩

end MatedCRT
