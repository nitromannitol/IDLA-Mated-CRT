import MatedCRT.FirstPass.Derived.ExitDecomposition
import MatedCRT.FirstPass.Derived.StoppedInterpPrefixCoupling

/-!
# Interpolation of stopped discrete paths

A stopped interpolated walk is determined by its stopped discrete path.
-/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition

namespace MatedCRT

/-- Stopping the discrete path first does not change its stopped interpolation. -/
theorem stoppedInterp_stoppedPath (v : ℤ → ℂ) (m : ℝ≥0) (A : Set ℤ)
    (x : ℕ → ℤ) :
    stoppedInterp v m A (stoppedPath A x) = stoppedInterp v m A x := by
  apply stoppedInterp_eq_of_exitTime_eq_of_prefix_eq
  · exact vExitTime_stoppedPath A x
  · intro j hj
    have hj' : (j : ℕ∞) ≤ vExitTime A x := by
      simpa only [vExitTime_stoppedPath] using hj
    simp [stoppedPath, min_eq_right hj']

/-- Equal laws of stopped discrete paths give equal stopped interpolation laws. -/
theorem stoppedInterp_law_eq_of_stoppedPath_law_eq (v : ℤ → ℂ) (m : ℝ≥0)
    (A : Set ℤ) (μ ν : Measure (ℕ → ℤ))
    (h : μ.map (stoppedPath A) = ν.map (stoppedPath A)) :
    μ.map (stoppedInterp v m A) = ν.map (stoppedInterp v m A) := by
  have h' := congrArg (fun ρ : Measure (ℕ → ℤ) => ρ.map (stoppedInterp v m A)) h
  rw [Measure.map_map (measurable_stoppedInterp v m A) (measurable_stoppedPath A),
    Measure.map_map (measurable_stoppedInterp v m A) (measurable_stoppedPath A)] at h'
  simpa only [Function.comp_def, stoppedInterp_stoppedPath] using h'

end MatedCRT
