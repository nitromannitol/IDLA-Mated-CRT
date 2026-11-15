import MatedCRT.FirstPass.Derived.ShiftedPaperWalkDilation
import MatedCRT.FirstPass.Derived.EmbeddedWalkIntegerShiftLaw

/-! # Scaling laws of shifted embedded walks -/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace MatedCRT

/-- Simultaneously dilating the boundary paths, mesh and embedding curve
transforms the shifted embedded walk law by spatial multiplication. -/
theorem interpolatedWalkLaw_shiftedPhysical_rescale
    {ε b c : ℝ} (hb : 0 < b) (hc : 0 < c) (θ : ℝ)
    (w w' : MatedCRTHarmonic.MatedCRT.Path2)
    (hw : ∀ t, w' t = (c * (w (b * t)).1, c * (w (b * t)).2))
    (R : ℂ) (η η' : ℝ → ℂ) (hη : ∀ t, η' t = R⁻¹ * η (b * t))
    (m : ℝ) (k : ℤ) :
    (srwLaw (bmEdgeCount (ε / b) (fun t => (w' (t + (ε / b) * θ)).1)
      (fun t => (w' (t + (ε / b) * θ)).2)) k).map
        (interpolatedWalk (ε / b) (fun t => η' (t + (ε / b) * θ)) m) =
    ((srwLaw (bmEdgeCount ε (fun t => (w (t + ε * θ)).1)
      (fun t => (w (t + ε * θ)).2)) k).map
        (interpolatedWalk ε (fun t => η (t + ε * θ)) m)).map
          (fun p t => R⁻¹ * p t) := by
  have hscale : Measurable (fun p : ℝ≥0 → ℂ => fun t => R⁻¹ * p t) :=
    Measurable.of_eval fun t => measurable_const.mul (measurable_pi_apply t)
  have hpath := measurable_interpolatedWalk_path ε (fun t => η (t + ε * θ)) m
  rw [srwLaw_shiftedPhysical_rescale hb hc θ w w' hw k, Measure.map_map hscale hpath]
  congr 1
  funext x t
  exact interpolatedWalk_shiftedPhysical_rescale hb θ R η η' hη m x t

end MatedCRT
