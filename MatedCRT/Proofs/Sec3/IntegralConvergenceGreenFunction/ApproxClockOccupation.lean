import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ClockOccupationSubstitution
import MatedCRT.Proofs.LBM.TimeChangeContinuity

/-! # Occupation identity for a regularized LQG clock -/

namespace MatedCRT

open MeasureTheory Set HarmonicBalls MarkovProcess
open scoped NNReal

/-- If a circle-average approximation is a time-change clock, its pathwise
occupation integral is the Brownian occupation weighted by the clock
density. This statement applies on each realization for which the indicated
clock regularity holds. -/
theorem lqgClockApprox_occupation_substitution
    (γ ε : ℝ) (hε : ℝ → ℂ → ℝ) (b : ContinuousPath ℂ)
    (hfield : Continuous (hε ε))
    (hclock : IsTimeChangeClock (lqgClockApprox γ hε ε b))
    (T : ℝ≥0) (f : ℂ → ℝ) (hf : Continuous f) :
    (∫ t in (0 : ℝ)..(T : ℝ), f (b t.toNNReal) *
      (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (b t.toNNReal)))) =
    ∫ s in (0 : ℝ)..(lqgClockApprox γ hε ε b T),
      f (b (clockInverse (lqgClockApprox γ hε ε b) s.toNNReal)) := by
  let a : ℝ → ℝ := fun t => ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (b t.toNNReal))
  let A : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, a s
  have ha : Continuous a := by
    dsimp [a]
    fun_prop
  have hA : Continuous A := (intervalIntegral.differentiable_integral_of_continuous ha).continuous
  have hderiv : ∀ t, HasDerivAt A (a t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right (ha.intervalIntegrable _ _)
      ha.aestronglyMeasurable.stronglyMeasurableAtFilter ha.continuousAt
  have hq : Continuous (fun s : ℝ => b (clockInverse (lqgClockApprox γ hε ε b) s.toNNReal)) :=
    b.continuous.comp ((IsTimeChangeClock.continuous_clockInverse hclock).comp continuous_real_toNNReal)
  have htrack : ∀ t ∈ Icc (0 : ℝ) (T : ℝ),
      b (clockInverse (lqgClockApprox γ hε ε b) (A t).toNNReal) = b t.toNNReal := by
    intro t ht
    have hAt : A t = lqgClockApprox γ hε ε b t.toNNReal := by
      simp [A, a, lqgClockApprox, Real.coe_toNNReal _ ht.1]
    rw [hAt, clockInverse_clockValue hclock.map_zero hclock.strictMono]
  have h := clock_occupation_substitution T.coe_nonneg A a
    (fun t => b t.toNNReal)
    (fun s => b (clockInverse (lqgClockApprox γ hε ε b) s.toNNReal)) f
    (by simp [A]) hA.continuousOn (fun t _ => (hderiv t).hasDerivWithinAt)
    ha.continuousOn hq.continuousOn hf htrack
  simpa [A, a, lqgClockApprox] using h

end MatedCRT
