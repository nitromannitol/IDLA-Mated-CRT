import MatedCRT.FirstPass.Derived.ShiftedPaperMultiplicity
import Mathlib.MeasureTheory.Function.AEMeasurableOrder

/-! # Measurability of shifted paper cell multiplicities -/

set_option autoImplicit false

open Set MeasureTheory

namespace MatedCRT

/-- The component-count array of the shifted cells transfers its almost-everywhere
measurability to the paper multiplicity array for the time-shifted curve. -/
theorem aemeasurable_cellMult_timeShift_of_shifted_component_array
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ)
    (hε : ∀ᵐ ω ∂μ, 0 ≤ ε ω)
    (h : AEMeasurable (fun ω (j k : ℤ) =>
      if j = k then 0 else
        {C ∈ HarmonicBalls.connectedComponentsIn
          ((LatticeProb.shiftedCompactCell (η ω) (ε ω) (θ ω) j : Set ℂ) ∩
            (LatticeProb.shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ)) |
            ¬ C.Subsingleton}.ncard) μ) :
    AEMeasurable (fun ω (j k : ℤ) =>
      cellMult (ε ω) (fun t => η ω (t + ε ω * θ ω)) j k) μ := by
  apply h.congr
  filter_upwards [hε] with ω hω
  funext j k
  exact shifted_cell_component_count_eq_cellMult_timeShift (η ω) hω (θ ω) j k

end MatedCRT
