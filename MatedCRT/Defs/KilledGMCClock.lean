import HarmonicBalls.Defs.LBM

/-!
# Killed Gaussian multiplicative chaos clocks

Clock stopped at Brownian exit as in Berestycki, *Diffusion in planar
Liouville quantum gravity*, arXiv:1301.3356, equations (2) and the display
in Section 1.2, p. 949.
-/

namespace MatedCRT

open HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

/-- The circle-average clock stopped at the first exit of `D`. The minimum
is taken in extended nonnegative time, so an infinite exit causes no
premature stopping. -/
noncomputable def killedGMCClockApprox (D : Set ℂ) (γ : ℝ)
    (hε : ℝ → ℂ → ℝ) (ε : ℝ) (b : ContinuousPath ℂ) (t : ℝ≥0) : ℝ :=
  lqgClockApprox γ hε ε b (min (t : ℝ≥0∞) (ContinuousPath.exitTime D b)).toNNReal

/-- Before exit, the killed approximation agrees with the original LQG
clock approximation. -/
theorem killedGMCClockApprox_eq_before_exit (D : Set ℂ) (γ : ℝ)
    (hε : ℝ → ℂ → ℝ) (ε : ℝ) (b : ContinuousPath ℂ) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) ≤ ContinuousPath.exitTime D b) :
    killedGMCClockApprox D γ hε ε b t = lqgClockApprox γ hε ε b t := by
  simp [killedGMCClockApprox, min_eq_left ht]

/-- The right-continuous inverse of a clock stopped at a (possibly infinite)
exit time. The infimum of an empty set is `∞`, and the minimum stops the
inverse at the exit time once the total clock mass has been exhausted. -/
noncomputable def killedClockInverse (F : ℝ≥0 → ℝ) (τ : ℝ≥0∞) (t : ℝ≥0) : ℝ≥0∞ :=
  min τ (⨅ (s : ℝ≥0) (_ : (t : ℝ) < F s), (s : ℝ≥0∞))

end MatedCRT
