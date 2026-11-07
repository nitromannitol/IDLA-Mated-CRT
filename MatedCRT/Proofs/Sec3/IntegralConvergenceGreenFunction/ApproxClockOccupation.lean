import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ClockOccupationSubstitution
import MatedCRT.Proofs.LBM.TimeChangeContinuity
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.StoppedClockExtension

/-! # Occupation identity for a regularized LQG clock -/

namespace MatedCRT

open MeasureTheory Set HarmonicBalls MarkovProcess
open scoped NNReal

/-- A circle-average clock with continuous field is continuous. -/
theorem lqgClockApprox_continuous
    (γ ε : ℝ) (hε : ℝ → ℂ → ℝ) (b : ContinuousPath ℂ)
    (hfield : Continuous (hε ε)) : Continuous (lqgClockApprox γ hε ε b) := by
  let a : ℝ → ℝ := fun t => ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (b t.toNNReal))
  have ha : Continuous a := by
    dsimp [a]
    fun_prop
  exact (intervalIntegral.differentiable_integral_of_continuous ha).continuous.comp
    continuous_subtype_val

/-- A circle-average clock at positive scale is strictly increasing, even
when its lifetime is finite. -/
theorem lqgClockApprox_strictMono
    (γ ε : ℝ) (hε : ℝ → ℂ → ℝ) (b : ContinuousPath ℂ)
    (hεpos : 0 < ε) (hfield : Continuous (hε ε)) :
    StrictMono (lqgClockApprox γ hε ε b) := by
  let a : ℝ → ℝ := fun t => ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (b t.toNNReal))
  have ha : Continuous a := by
    dsimp [a]
    fun_prop
  have hapos : ∀ t, 0 < a t := by
    intro t
    exact mul_pos (Real.rpow_pos_of_pos hεpos _) (Real.exp_pos _)
  intro s t hst
  have hst' : (s : ℝ) < t := by exact_mod_cast hst
  have hp : 0 < ∫ x in (s : ℝ)..(t : ℝ), a x :=
    intervalIntegral.integral_pos hst' ha.continuousOn
      (fun x _ => (hapos x).le) ⟨s, ⟨le_rfl, hst'.le⟩, hapos s⟩
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (ha.intervalIntegrable (μ := volume) 0 s) (ha.intervalIntegrable (μ := volume) s t)
  change (∫ x in (0 : ℝ)..(s : ℝ), a x) < ∫ x in (0 : ℝ)..(t : ℝ), a x
  linarith

/-- For a positive-scale circle-average clock, divergence at infinity is
the remaining condition for an infinite-lifetime time change. -/
theorem isTimeChangeClock_lqgClockApprox_of_tendsto
    (γ ε : ℝ) (hε : ℝ → ℂ → ℝ) (b : ContinuousPath ℂ)
    (hεpos : 0 < ε) (hfield : Continuous (hε ε))
    (hinf : Filter.Tendsto (lqgClockApprox γ hε ε b) Filter.atTop Filter.atTop) :
    IsTimeChangeClock (lqgClockApprox γ hε ε b) := by
  refine ⟨?_, lqgClockApprox_continuous γ ε hε b hfield,
    lqgClockApprox_strictMono γ ε hε b hεpos hfield, hinf⟩
  simp [lqgClockApprox]

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

/-- The regularized occupation identity on a finite time interval requires
no assumption on the lifetime of the regularized clock. -/
theorem lqgClockApprox_occupation_substitution_local
    (γ ε : ℝ) (hε : ℝ → ℂ → ℝ) (b : ContinuousPath ℂ)
    (hεpos : 0 < ε) (hfield : Continuous (hε ε))
    (T : ℝ≥0) (f : ℂ → ℝ) (hf : Continuous f) :
    (∫ t in (0 : ℝ)..(T : ℝ), f (b t.toNNReal) *
      (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (b t.toNNReal)))) =
    ∫ s in (0 : ℝ)..(lqgClockApprox γ hε ε b T),
      f (b (clockInverse (lqgClockApprox γ hε ε b) s.toNNReal)) := by
  let F := lqgClockApprox γ hε ε b
  let G := stoppedClockExtension F T
  have hzero : F 0 = 0 := by simp [F, lqgClockApprox]
  have hcont : Continuous F := lqgClockApprox_continuous γ ε hε b hfield
  have hmono : StrictMono F := lqgClockApprox_strictMono γ ε hε b hεpos hfield
  have hG : IsTimeChangeClock G := stoppedClockExtension_isTimeChangeClock T hzero hcont hmono
  have hnonneg : 0 ≤ F T := by simpa [hzero] using hmono.monotone (show 0 ≤ T from bot_le)
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
  have hq : Continuous (fun s : ℝ => b (clockInverse G s.toNNReal)) :=
    b.continuous.comp ((IsTimeChangeClock.continuous_clockInverse hG).comp continuous_real_toNNReal)
  have htrack : ∀ t ∈ Icc (0 : ℝ) (T : ℝ),
      b (clockInverse G (A t).toNNReal) = b t.toNNReal := by
    intro t ht
    have hAt : A t = F t.toNNReal := by
      simp [A, a, F, lqgClockApprox, Real.coe_toNNReal _ ht.1]
    have ht' : t.toNNReal ≤ T := by
      apply NNReal.coe_le_coe.mp
      simpa [Real.coe_toNNReal _ ht.1] using ht.2
    rw [hAt, ← stoppedClockExtension_eq (F := F) ht', ← show G = stoppedClockExtension F T from rfl,
      clockInverse_clockValue hG.map_zero hG.strictMono]
  have h := clock_occupation_substitution T.coe_nonneg A a
    (fun t => b t.toNNReal) (fun s => b (clockInverse G s.toNNReal)) f
    (by simp [A]) hA.continuousOn (fun t _ => (hderiv t).hasDerivWithinAt)
    ha.continuousOn hq.continuousOn hf htrack
  have heq : (∫ s in (0 : ℝ)..F T, f (b (clockInverse G s.toNNReal))) =
      ∫ s in (0 : ℝ)..F T, f (b (clockInverse F s.toNNReal)) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hnonneg]
    intro s hs
    have hs' : (s.toNNReal : ℝ) ≤ F T := by simpa [Real.coe_toNNReal _ hs.1] using hs.2
    change f (b (clockInverse (stoppedClockExtension F T) s.toNNReal)) = _
    rw [stoppedClockExtension_inverse_eq hzero hcont hmono hs']
  have hAT : A T = F T := by simp [A, a, F, lqgClockApprox]
  rw [hAT] at h
  rw [heq] at h
  simpa [A, a, F, lqgClockApprox] using h

end MatedCRT
