import MatedCRT.FirstPass.Derived.ShiftedPaperMultiplicityObservable
import LatticeProb.Topology.RandomShiftedCellAEComponentArray

/-! # Shifted cell multiplicities under pairwise component bounds -/

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace

namespace MatedCRT

/-- Pairwise almost-everywhere component bounds imply measurability of the
multiplicity array of the time-shifted curve. -/
theorem aemeasurable_cellMult_timeShift_of_pairwise_components
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (hη : AEMeasurable η μ) (hε : AEMeasurable ε μ) (hθ : AEMeasurable θ μ)
    (hε_nonneg : ∀ᵐ ω ∂μ, 0 ≤ ε ω)
    (h : ∀ k l : ℤ, k ≠ l → ∀ᵐ ω ∂μ,
      let S : Set ℂ := (LatticeProb.shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ) ∩
        LatticeProb.shiftedCompactCell (η ω) (ε ω) (θ ω) l
      ¬ ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S,
        connectedComponentIn S x ≠ connectedComponentIn S y ∧
        connectedComponentIn S x ≠ connectedComponentIn S z ∧
        connectedComponentIn S y ≠ connectedComponentIn S z ∧
        ¬ (connectedComponentIn S x).Subsingleton ∧
        ¬ (connectedComponentIn S y).Subsingleton ∧
        ¬ (connectedComponentIn S z).Subsingleton) :
    AEMeasurable (fun ω (j k : ℤ) =>
      cellMult (ε ω) (fun t => η ω (t + ε ω * θ ω)) j k) μ := by
  apply aemeasurable_cellMult_timeShift_of_shifted_component_array μ η ε θ hε_nonneg
  simpa only [LatticeProb.nonSingletonComponents, HarmonicBalls.connectedComponentsIn] using
    LatticeProb.aemeasurable_shifted_cell_component_array_of_pairwise_ae η ε θ μ hη hε hθ h

end MatedCRT
