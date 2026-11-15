import MatedCRT.FirstPass.Derived.ShiftedPaperCell
import LatticeProb.Topology.RandomShiftedCellComponentEvent
import LatticeProb.Topology.RandomShiftedCellTwoComponentsEvent

/-! # Component events for translated cells -/

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace

namespace MatedCRT

/-- The event that two translated cells share a non-singleton connected component
is null measurable for a nonnegative random mesh. -/
theorem nullMeasurableSet_translated_cell_inter_component
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ) (k l : ℤ)
    (hη : Measurable η) (hε : Measurable ε) (hθ : Measurable θ)
    (μ : Measure Ω) [IsFiniteMeasure μ] (hε₀ : ∀ᵐ ω ∂μ, 0 ≤ ε ω) :
    NullMeasurableSet {ω : Ω |
      let S := cell (ε ω) (fun t => η ω (t + ε ω * θ ω)) k ∩
        cell (ε ω) (fun t => η ω (t + ε ω * θ ω)) l
      ∃ C ∈ connectedComponentIn S '' S, ¬ C.Subsingleton} μ := by
  apply (LatticeProb.nullMeasurableSet_random_shifted_cell_inter_component
    η ε θ k l hη hε hθ μ).congr
  filter_upwards [hε₀] with ω hω
  rw [shiftedCompactCell_eq_cell_timeShift (η ω) hω (θ ω) k,
    shiftedCompactCell_eq_cell_timeShift (η ω) hω (θ ω) l]

/-- The event that two translated cells share two distinct non-singleton connected
components is null measurable for a nonnegative random mesh. -/
theorem nullMeasurableSet_translated_cell_inter_two_components
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ) (k l : ℤ)
    (hη : Measurable η) (hε : Measurable ε) (hθ : Measurable θ)
    (μ : Measure Ω) [IsFiniteMeasure μ] (hε₀ : ∀ᵐ ω ∂μ, 0 ≤ ε ω) :
    NullMeasurableSet {ω : Ω |
      let S := cell (ε ω) (fun t => η ω (t + ε ω * θ ω)) k ∩
        cell (ε ω) (fun t => η ω (t + ε ω * θ ω)) l
      ∃ x ∈ S, ∃ y ∈ S,
        connectedComponentIn S x ≠ connectedComponentIn S y ∧
        ¬ (connectedComponentIn S x).Subsingleton ∧
        ¬ (connectedComponentIn S y).Subsingleton} μ := by
  apply (LatticeProb.nullMeasurableSet_random_shifted_cell_inter_two_components
    η ε θ k l hη hε hθ μ).congr
  filter_upwards [hε₀] with ω hω
  rw [shiftedCompactCell_eq_cell_timeShift (η ω) hω (θ ω) k,
    shiftedCompactCell_eq_cell_timeShift (η ω) hω (θ ω) l]

end MatedCRT
