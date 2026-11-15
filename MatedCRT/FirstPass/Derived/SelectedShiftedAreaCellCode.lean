import MatedCRT.FirstPass.Derived.ShiftedAreaCellCode

/-! # Codes of selected shifted area-cell configurations -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory ReflectedGMS.GMS

/-- An almost-everywhere valid shifted area-cell configuration can be selected
with an almost-everywhere measurable code. -/
theorem exists_shiftedAreaCellConfig_aemeasurable_code
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    {ε : ℝ} (hε : 0 < ε) (η : Ω → C(ℝ, ℂ)) (w : Ω → C(ℝ, ℝ × ℝ))
    (θ : Ω → ℝ) (μ : Ω → Measure ℂ)
    (hη : Measurable η) (hw : Measurable w) (hθ : Measurable θ)
    (hvalid : ∀ᵐ ω ∂P, ∃ h : IsAreaParametrized (μ ω) (η ω),
      (shiftedAreaCellConfig h hε (θ ω)
        (bmEdgeCount ε (fun t => (w ω (t + ε * θ ω)).1)
          (fun t => (w ω (t + ε * θ ω)).2))).IsCellConfiguration) :
    ∃ H : Ω → CellConfig,
      (∀ᵐ ω ∂P, ∃ h : IsAreaParametrized (μ ω) (η ω),
        H ω = shiftedAreaCellConfig h hε (θ ω)
          (bmEdgeCount ε (fun t => (w ω (t + ε * θ ω)).1)
            (fun t => (w ω (t + ε * θ ω)).2)) ∧ (H ω).IsCellConfiguration) ∧
      AEMeasurable (fun ω => (H ω).code) P := by
  classical
  let M : Ω → ℤ → ℤ → ℕ := fun ω =>
    bmEdgeCount ε (fun t => (w ω (t + ε * θ ω)).1)
      (fun t => (w ω (t + ε * θ ω)).2)
  let H : Ω → CellConfig := fun ω =>
    if h : ∃ h : IsAreaParametrized (μ ω) (η ω),
        (shiftedAreaCellConfig h hε (θ ω) (M ω)).IsCellConfiguration then
      shiftedAreaCellConfig (Classical.choose h) hε (θ ω) (M ω)
    else ⟨∅, fun _ _ => 0⟩
  have hH : ∀ᵐ ω ∂P, ∃ h : IsAreaParametrized (μ ω) (η ω),
      H ω = shiftedAreaCellConfig h hε (θ ω) (M ω) ∧ (H ω).IsCellConfiguration := by
    filter_upwards [hvalid] with ω hω
    have hv : ∃ h : IsAreaParametrized (μ ω) (η ω),
        (shiftedAreaCellConfig h hε (θ ω) (M ω)).IsCellConfiguration := hω
    refine ⟨Classical.choose hv, ?_, ?_⟩
    · simp only [H, dite_eq_left hv]
    · simpa only [H, dite_eq_left hv] using Classical.choose_spec hv
  refine ⟨H, hH, ?_⟩
  exact aemeasurable_shiftedAreaCellConfig_code P hε η w θ μ H hη hw hθ hH

end MatedCRT
