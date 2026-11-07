import MatedCRT.Defs.KilledGMCClock

/-! # Localization of convergence of Liouville clocks -/

namespace MatedCRT

open HarmonicBalls MarkovProcess MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

/-- Stopping preserves the uniform-on-compacts convergence in probability
in `IsLQGClock`. The stopping time may depend on the whole path, and may be
infinite; measurability is not required for this outer-probability bound. -/
theorem IsLQGClock.stopped_uniform_in_probability
    {Q : Kernel ℂ (ContinuousPath ℂ)} {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    {x : ℂ} {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hclock : IsLQGClock Q γ hε x F) (τ : ContinuousPath ℂ → ℝ≥0∞)
    (T : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ => Q x {b | ∃ t ≤ T,
      η ≤ |lqgClockApprox γ hε (dyadicScale n) b
          (min (t : ℝ≥0∞) (τ b)).toNNReal -
        F b (min (t : ℝ≥0∞) (τ b)).toNNReal|}) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hclock T η hη) (fun _ => bot_le) ?_
  intro n
  apply measure_mono
  rintro b ⟨t, ht, hdiff⟩
  refine ⟨(min (t : ℝ≥0∞) (τ b)).toNNReal, ?_, hdiff⟩
  have hle : (min (t : ℝ≥0∞) (τ b)).toNNReal ≤ t := by
    simpa using ENNReal.toNNReal_mono ENNReal.coe_ne_top (min_le_left (t : ℝ≥0∞) (τ b))
  exact hle.trans ht

/-- The stopped circle-average approximations converge to the global LQG
clock stopped on leaving the domain, uniformly on compact time intervals. -/
theorem IsLQGClock.killed_uniform_in_probability
    {Q : Kernel ℂ (ContinuousPath ℂ)} {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    {x : ℂ} {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hclock : IsLQGClock Q γ hε x F) (D : Set ℂ)
    (T : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ => Q x {b | ∃ t ≤ T,
      η ≤ |killedGMCClockApprox D γ hε (dyadicScale n) b t -
        F b (min (t : ℝ≥0∞) (ContinuousPath.exitTime D b)).toNNReal|}) atTop (𝓝 0) := by
  simpa only [killedGMCClockApprox] using
    IsLQGClock.stopped_uniform_in_probability hclock (ContinuousPath.exitTime D) T hη

end MatedCRT
