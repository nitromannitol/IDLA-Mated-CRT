import MatedCRT.FirstPass.Derived.PaperCellMultiplicityScaling
import MatedCRT.FirstPass.Derived.ShiftedEmbeddedMeasureDilation

/-! # Scaling of embedded cell walk laws -/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace MatedCRT

/-- Spatial dilation transforms the embedded walk law on the translated cell grid. -/
theorem interpolatedCellWalkLaw_shiftedPhysical_rescale
    {ε b : ℝ} {R : ℂ} (hb : 0 < b) (hR : R ≠ 0) (θ : ℝ)
    (η η' : ℝ → ℂ) (hη : ∀ t, η' t = R⁻¹ * η (b * t))
    (speed : ℝ) (k : ℤ) :
    (srwLaw (cellMult (ε / b) (fun t => η' (t + (ε / b) * θ))) k).map
        (interpolatedWalk (ε / b) (fun t => η' (t + (ε / b) * θ)) speed) =
      ((srwLaw (cellMult ε (fun t => η (t + ε * θ))) k).map
        (interpolatedWalk ε (fun t => η (t + ε * θ)) speed)).map
          (fun p t => R⁻¹ * p t) := by
  have hmult : cellMult (ε / b) (fun t => η' (t + (ε / b) * θ)) =
      cellMult ε (fun t => η (t + ε * θ)) := by
    funext j l
    exact cellMult_shiftedPhysical_rescale hb hR θ η η' hη j l
  rw [hmult]
  exact interpolatedWalk_map_shiftedPhysical_rescale hb θ R η η' hη speed _

end MatedCRT
