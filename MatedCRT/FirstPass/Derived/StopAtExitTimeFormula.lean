import MatedCRT.FirstPass.S6j.LitUniformStartInvariance

/-! # Stopping at an exit time -/

set_option autoImplicit false

open HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT

/-- Stopping at an exit agrees with evaluating at the minimum of the observation
and exit times, including when the exit time is infinite. -/
theorem stopAtExit_eq_min_exitTime (U : Set ℂ) (f : ℝ≥0 → ℂ) (t : ℝ≥0) :
    stopAtExit U f t = f (min (t : ℝ≥0∞) (pathExitTime U f)).toNNReal := by
  by_cases h : pathExitTime U f = ⊤
  · simp only [stopAtExit, h, ↓reduceIte, min_eq_left le_top, ENNReal.toNNReal_coe]
  · obtain ⟨u, hu⟩ : ∃ u : ℝ≥0, (u : ℝ≥0∞) = pathExitTime U f :=
      ⟨_, ENNReal.coe_toNNReal h⟩
    simp only [stopAtExit, h, ↓reduceIte]
    rw [← hu, ENNReal.toNNReal_coe, ← ENNReal.coe_min, ENNReal.toNNReal_coe]

end MatedCRT
