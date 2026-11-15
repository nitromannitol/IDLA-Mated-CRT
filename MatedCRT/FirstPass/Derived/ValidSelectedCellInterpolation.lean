import MatedCRT.FirstPass.Derived.ValidCountableShiftedAreaCellWalk
import MatedCRT.FirstPass.Derived.ShiftedOriginSelectedVertex
import MatedCRT.FirstPass.Derived.ShiftedSelectedCellInterpolation

/-! # Interpolation of shifted origin cell walks in valid environments -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTInput
open scoped NNReal

/-- For countably many meshes and fixed absolutely continuous phase laws, the
selected origin walk is the interpolation of any cell walk from label zero,
on the same sample and phase events as the shifted cell configuration. -/
theorem MatedCRTEnv.IsValid.ae_countable_phaseSelectedCellInterpolation
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
          let M := bmEdgeCount (ε i) (fun t => (w t).1) (fun t => (w t).2)
          let C := shiftedAreaCellConfig h (hε i) (c / ε i) M
          C.IsCellConfiguration ∧ C.LineConnected ∧
          (∀ a : ℤ, C.IsSRWLaw (shiftedEuclideanCellEquiv h (hε i) (c / ε i) a)
            ((srwLaw M a).map (fun p n => shiftedEuclideanCellEquiv h (hε i) (c / ε i) (p n)))) ∧
          ∀ (R : Measure (ℕ → C.cells)),
            C.IsSRWLaw (shiftedEuclideanCellEquiv h (hε i) (c / ε i) 0) R →
            ∀ m : ℝ≥0, shiftedSelectedWalkLaw (ε i) m c 0 (S.η ω) (S.bm ω) =
              R.map (fun p => interpPathCM (vertexPoint (ε i) (fun t => S.η ω (t + c)))
                m.coe_nonneg (fun n => (shiftedEuclideanCellEquiv h (hε i) (c / ε i)).symm (p n))) := by
  filter_upwards [hS.ae_countable_phaseAreaCellWalk hγ ε hε Q hQ hQmem,
    hS.ae_vertexOf_shifted_origin] with ω hw hv
  obtain ⟨h, hw⟩ := hw
  refine ⟨h, fun i => ?_⟩
  have h0 : ∀ᵐ c ∂Q i, c ≠ 0 := (hQ i).ae_le (Measure.ae_ne volume 0)
  have h1 : ∀ᵐ c ∂Q i, c ≠ ε i := (hQ i).ae_le (Measure.ae_ne volume (ε i))
  filter_upwards [hw i, hQmem i, h0, h1] with c hc hmem hc0 hc1
  obtain ⟨hlf, H, hcell, hconfig, hconnected, hwalk⟩ := hc
  refine ⟨hlf, H, hcell, hconfig, hconnected, hwalk, ?_⟩
  intro R hR m
  have hvertex := hv (ε i) (hε i) c
    (lt_of_le_of_ne hmem.1 (Ne.symm hc0)) (lt_of_le_of_ne hmem.2 hc1)
  apply shiftedSelectedWalkLaw_eq_map_cellWalk h (hε i) c (S.bm ω) 0 m hlf R
  rw [hvertex]
  exact hR

end MatedCRT
end
