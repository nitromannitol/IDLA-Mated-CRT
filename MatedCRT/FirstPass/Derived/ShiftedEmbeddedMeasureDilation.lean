import MatedCRT.FirstPass.Derived.ShiftedPaperWalkDilation
import MatedCRT.FirstPass.Derived.EmbeddedWalkIntegerShiftLaw

/-! # Spatial scaling of interpolated path measures -/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace MatedCRT

/-- Spatial scaling commutes with the embedded interpolation of any measure
on integer paths, on corresponding translated time grids. -/
theorem interpolatedWalk_map_shiftedPhysical_rescale
    {ε b : ℝ} (hb : 0 < b) (θ : ℝ) (R : ℂ) (η η' : ℝ → ℂ)
    (hη : ∀ t, η' t = R⁻¹ * η (b * t)) (speed : ℝ)
    (μ : Measure (ℕ → ℤ)) :
    μ.map (interpolatedWalk (ε / b) (fun t => η' (t + (ε / b) * θ)) speed) =
      (μ.map (interpolatedWalk ε (fun t => η (t + ε * θ)) speed)).map
        (fun p t => R⁻¹ * p t) := by
  have hscale : Measurable (fun p : ℝ≥0 → ℂ => fun t => R⁻¹ * p t) :=
    Measurable.of_eval fun t => measurable_const.mul (measurable_pi_apply t)
  have hpath := measurable_interpolatedWalk_path ε (fun t => η (t + ε * θ)) speed
  rw [Measure.map_map hscale hpath]
  congr 1
  funext x t
  exact interpolatedWalk_shiftedPhysical_rescale hb θ R η η' hη speed x t

end MatedCRT
