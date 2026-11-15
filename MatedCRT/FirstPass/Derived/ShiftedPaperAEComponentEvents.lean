import MatedCRT.FirstPass.Derived.ShiftedPaperComponentEvents

/-! # Component events for almost-everywhere measurable translated cells -/

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace

namespace MatedCRT

/-- The non-singleton component event is null measurable for almost-everywhere
measurable curve, mesh, and phase inputs. -/
theorem nullMeasurableSet_translated_cell_inter_component_of_ae
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ) (k l : ℤ)
    (μ : Measure Ω) [IsFiniteMeasure μ] (hη : AEMeasurable η μ)
    (hε : AEMeasurable ε μ) (hθ : AEMeasurable θ μ)
    (hε₀ : ∀ᵐ ω ∂μ, 0 ≤ ε ω) :
    NullMeasurableSet {ω : Ω |
      let S := cell (ε ω) (fun t => η ω (t + ε ω * θ ω)) k ∩
        cell (ε ω) (fun t => η ω (t + ε ω * θ ω)) l
      ∃ C ∈ connectedComponentIn S '' S, ¬ C.Subsingleton} μ := by
  let η' := hη.mk η
  let ε' := hε.mk ε
  let θ' := hθ.mk θ
  have hε₀' : ∀ᵐ ω ∂μ, 0 ≤ ε' ω := by
    filter_upwards [hε₀, hε.ae_eq_mk] with ω hω heq
    simpa only [ε', ← heq] using hω
  apply (nullMeasurableSet_translated_cell_inter_component η' ε' θ' k l
    hη.measurable_mk hε.measurable_mk hθ.measurable_mk μ hε₀').congr
  filter_upwards [hη.ae_eq_mk, hε.ae_eq_mk, hθ.ae_eq_mk] with ω hηω hεω hθω
  simp only [η', ε', θ', ← hηω, ← hεω, ← hθω]

/-- The event of two distinct non-singleton components is null measurable for
almost-everywhere measurable curve, mesh, and phase inputs. -/
theorem nullMeasurableSet_translated_cell_inter_two_components_of_ae
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ) (k l : ℤ)
    (μ : Measure Ω) [IsFiniteMeasure μ] (hη : AEMeasurable η μ)
    (hε : AEMeasurable ε μ) (hθ : AEMeasurable θ μ)
    (hε₀ : ∀ᵐ ω ∂μ, 0 ≤ ε ω) :
    NullMeasurableSet {ω : Ω |
      let S := cell (ε ω) (fun t => η ω (t + ε ω * θ ω)) k ∩
        cell (ε ω) (fun t => η ω (t + ε ω * θ ω)) l
      ∃ x ∈ S, ∃ y ∈ S,
        connectedComponentIn S x ≠ connectedComponentIn S y ∧
        ¬ (connectedComponentIn S x).Subsingleton ∧
        ¬ (connectedComponentIn S y).Subsingleton} μ := by
  let η' := hη.mk η
  let ε' := hε.mk ε
  let θ' := hθ.mk θ
  have hε₀' : ∀ᵐ ω ∂μ, 0 ≤ ε' ω := by
    filter_upwards [hε₀, hε.ae_eq_mk] with ω hω heq
    simpa only [ε', ← heq] using hω
  apply (nullMeasurableSet_translated_cell_inter_two_components η' ε' θ' k l
    hη.measurable_mk hε.measurable_mk hθ.measurable_mk μ hε₀').congr
  filter_upwards [hη.ae_eq_mk, hε.ae_eq_mk, hθ.ae_eq_mk] with ω hηω hεω hθω
  simp only [η', ε', θ', ← hηω, ← hεω, ← hθω]

end MatedCRT
