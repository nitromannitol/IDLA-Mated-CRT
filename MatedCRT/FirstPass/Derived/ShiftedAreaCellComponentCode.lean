import MatedCRT.FirstPass.Derived.ShiftedAreaCellMultiplicityCode
import LatticeProb.Topology.RandomShiftedCellComponentCount

/-! # Codes of shifted area cells with component-count conductances -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS

/-- A valid shifted area-cell configuration has an almost-everywhere measurable
code when its conductances are the zero-diagonal intersection component counts. -/
theorem aemeasurable_shiftedAreaCellConfig_code_of_component_counts
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {ε : ℝ} (hε : 0 < ε) (η : Ω → C(ℝ, ℂ))
    (θ : Ω → ℝ) (μ : Ω → Measure ℂ) (H : Ω → CellConfig)
    (hη : Measurable η) (hθ : Measurable θ)
    (hH : let M : Ω → ℤ → ℤ → ℕ := fun ω j k => if j = k then 0 else
        (LatticeProb.nonSingletonComponents
          ((LatticeProb.shiftedCompactCell (η ω) ε (θ ω) j : Set ℂ) ∩
            LatticeProb.shiftedCompactCell (η ω) ε (θ ω) k)).ncard
      ∀ᵐ ω ∂P, ∃ h : IsAreaParametrized (μ ω) (η ω),
        H ω = shiftedAreaCellConfig h hε (θ ω) (M ω) ∧ (H ω).IsCellConfiguration) :
    AEMeasurable (fun ω => (H ω).code) P := by
  let M : Ω → ℤ → ℤ → ℕ := fun ω j k => if j = k then 0 else
    (LatticeProb.nonSingletonComponents
      ((LatticeProb.shiftedCompactCell (η ω) ε (θ ω) j : Set ℂ) ∩
        LatticeProb.shiftedCompactCell (η ω) ε (θ ω) k)).ncard
  have hM : AEMeasurable M P :=
    LatticeProb.aemeasurable_shifted_cell_component_array_of_ae η (fun _ => ε) θ P
      hη.aemeasurable aemeasurable_const hθ.aemeasurable
  apply aemeasurable_shiftedAreaCellConfig_code_of_multiplicity P hε η θ μ M H hη hθ
  · intro j k
    exact (hM.eval j).eval k
  · exact hH

end MatedCRT
