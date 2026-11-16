import MatedCRT.FirstPass.Derived.ShiftedAreaCellComponentCode
import MatedCRT.FirstPass.Derived.ShiftedPaperMultiplicity

/-! # Codes of shifted area cells with paper multiplicities -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS

/-- A valid shifted area-cell configuration has an almost-everywhere measurable
code when its conductances are the paper's intersection-component multiplicities. -/
theorem aemeasurable_shiftedAreaCellConfig_code_of_cellMult
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {ε : ℝ} (hε : 0 < ε) (η : Ω → C(ℝ, ℂ))
    (θ : Ω → ℝ) (μ : Ω → Measure ℂ) (H : Ω → CellConfig)
    (hη : Measurable η) (hθ : Measurable θ)
    (hH : ∀ᵐ ω ∂P, ∃ h : IsAreaParametrized (μ ω) (η ω),
      H ω = shiftedAreaCellConfig h hε (θ ω)
        (cellMult ε (fun t => η ω (t + ε * θ ω))) ∧ (H ω).IsCellConfiguration) :
    AEMeasurable (fun ω => (H ω).code) P := by
  apply aemeasurable_shiftedAreaCellConfig_code_of_component_counts P hε η θ μ H hη hθ
  filter_upwards [hH] with ω ⟨h, heq, hvalid⟩
  refine ⟨h, ?_, hvalid⟩
  have hm : (fun j k : ℤ => if j = k then 0 else
      (LatticeProb.nonSingletonComponents
        ((LatticeProb.shiftedCompactCell (η ω) ε (θ ω) j : Set ℂ) ∩
          LatticeProb.shiftedCompactCell (η ω) ε (θ ω) k)).ncard) =
      cellMult ε (fun t => η ω (t + ε * θ ω)) := by
    funext j k
    simpa only [LatticeProb.nonSingletonComponents, HarmonicBalls.connectedComponentsIn] using
      shifted_cell_component_count_eq_cellMult_timeShift (η ω) hε.le (θ ω) j k
  rw [hm]
  exact heq

end MatedCRT
