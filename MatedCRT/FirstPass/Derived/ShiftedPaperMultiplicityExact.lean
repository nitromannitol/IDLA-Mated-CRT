import MatedCRT.FirstPass.Derived.ShiftedPaperMultiplicityObservable
import LatticeProb.Topology.RandomShiftedCellComponentCount

/-! # Measurability of shifted cell multiplicities -/

set_option autoImplicit false

open Set MeasureTheory

namespace MatedCRT

/-- The multiplicity array of a time-shifted curve is almost everywhere measurable. -/
theorem aemeasurable_cellMult_timeShift
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (hη : AEMeasurable η μ) (hε : AEMeasurable ε μ) (hθ : AEMeasurable θ μ)
    (hε_nonneg : ∀ᵐ ω ∂μ, 0 ≤ ε ω) :
    AEMeasurable (fun ω (j k : ℤ) =>
      cellMult (ε ω) (fun t => η ω (t + ε ω * θ ω)) j k) μ := by
  apply aemeasurable_cellMult_timeShift_of_shifted_component_array μ η ε θ hε_nonneg
  simpa only [LatticeProb.nonSingletonComponents, HarmonicBalls.connectedComponentsIn] using
    LatticeProb.aemeasurable_shifted_cell_component_array_of_ae η ε θ μ hη hε hθ

end MatedCRT
