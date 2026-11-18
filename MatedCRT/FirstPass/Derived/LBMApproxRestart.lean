import MatedCRT.FirstPass.Derived.LBMPathRestart
import MatedCRT.FirstPass.Derived.ConeReferenceClockMarkovTransfer
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.CutoffPathUniform
import LatticeProb.Prob.KernelTVContraction

/-!
# Restarting the approximate Liouville Brownian motion at a deterministic time

Let `A_n = lqgApproxClockPlus γ h n` be the approximating LQG clock at the dyadic scale `2^{-n}`
(circle-average clock plus the drift `2^{-n} t`) and `Φ_n = lbmContinuousPath A_n` the
corresponding time-changed path map. Fix `δ ≥ 0` and write `θ_δ b = b (δ + ·)`.

* `lqgApproxClockPlus_add_eq_add_shift`: the clock is additive along every path,
  `A_n(b, δ + s) = A_n(b, δ) + A_n(θ_δ b, s)`.
* `lbmContinuousPath_lqgApproxClockPlus_clockValue_add`: after the clock value `c = A_n(b, δ)`,
  `Φ_n b (c + u) = Φ_n (θ_δ b) u`.
* `localUniformDist_lbmContinuousPath_pathDelay_le`: the path `Φ_n b` and the delayed path
  `T_c (Φ_n (θ_δ b))`, `T_c y (t) = y ((t - c)⁺)`, are within the oscillation of `b` on `[0, δ]` in
  the local uniform distance. This holds for every clock that is additive at `δ`.
* `planarBrownianMotion_map_shift`: the simple Markov property at the fixed time `δ`, the law of
  `θ_δ b` under `P^z` is the heat kernel at time `δ` from `z` composed with Brownian motion; hence
  `tvDist_planarBrownianMotion_map_shift_le` bounds the total variation distance of the laws of
  `θ_δ b` under two starting points by that of the heat kernels.

These are the deterministic and the Markov steps in the proof of the weak continuity in the
starting point of the law of Liouville Brownian motion (Garban–Rhodes–Vargas, *Liouville Brownian
motion*, Ann. Probab. 44 (2016), Proposition 2.19, for the massive free field).
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory ProbabilityTheory MarkovProcess Filter
open _root_.HarmonicBalls
open scoped NNReal

/-- The path `y` delayed by the time `c`: `(T_c y)(t) = y ((t - c)⁺)`. -/
def pathDelay (c : ℝ≥0) (y : ℝ≥0 → ℂ) : ℝ≥0 → ℂ := fun t => y (t - c)

@[simp] theorem pathDelay_apply (c : ℝ≥0) (y : ℝ≥0 → ℂ) (t : ℝ≥0) :
    pathDelay c y t = y (t - c) := rfl

/-- Paths within `η` at every time are within `η` in the local uniform distance. -/
theorem localUniformDist_le_of_forall_norm_le (f g : ℝ≥0 → ℂ) {η : ℝ} (hη : 0 ≤ η)
    (h : ∀ t, ‖f t - g t‖ ≤ η) : localUniformDist f g ≤ η := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hd := localUniformDist_le_add_of_forall_le f g K hη (fun t _ => h t)
  have hp : (2 : ℝ)⁻¹ ^ (K + 1) ≤ (2 : ℝ)⁻¹ ^ K :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ K)
  linarith

section Path

variable {F : ContinuousPath ℂ → ℝ≥0 → ℝ} {b : ContinuousPath ℂ} {δ : ℝ≥0}

/-- Under clock additivity at `δ`, the time-changed path of `b` is within the oscillation of `b`
on `[0, δ]` of the time-changed path of `θ_δ b` delayed by the clock value `F b δ`, at every time. -/
theorem norm_lbmContinuousPath_sub_pathDelay_le (hF : IsTimeChangeClock (F b))
    (hadd : ∀ s, F (ContinuousPath.shift δ b) s = F b (δ + s) - F b δ) {η : ℝ}
    (hosc : ∀ r ≤ δ, ‖b r - b δ‖ ≤ η) (t : ℝ≥0) :
    ‖lbmContinuousPath F b t -
      pathDelay (F b δ).toNNReal (lbmContinuousPath F (ContinuousPath.shift δ b)) t‖ ≤ η := by
  have hη : 0 ≤ η := (norm_nonneg _).trans (hosc δ le_rfl)
  rw [pathDelay_apply]
  rcases le_total (F b δ).toNNReal t with hct | htc
  · obtain ⟨u, rfl⟩ : ∃ u, t = (F b δ).toNNReal + u :=
      ⟨t - (F b δ).toNNReal, (add_tsub_cancel_of_le hct).symm⟩
    rw [add_tsub_cancel_left, lbmContinuousPath_clockValue_add hF hadd u, sub_self, norm_zero]
    exact hη
  · rw [tsub_eq_zero_of_le htc, lbmContinuousPath_of_isTimeChangeClock hF,
      lbmContinuousPath_of_isTimeChangeClock (isTimeChangeClock_shift hF hadd)]
    change ‖liouvilleBrownianPath F b t - liouvilleBrownianPath F (ContinuousPath.shift δ b) 0‖ ≤ η
    rw [liouvilleBrownianPath_shift_zero hF hadd]
    exact hosc _ (clockInverse_le_of_le_clockValue hF htc)

/-- **Comparison with the delayed restarted path.** Under clock additivity at `δ`, if `b`
oscillates by at most `η` on `[0, δ]` (relative to `b δ`), then the time-changed path of `b` and
the time-changed path of `θ_δ b` delayed by `F b δ` are within `η` in the local uniform
distance. -/
theorem localUniformDist_lbmContinuousPath_pathDelay_le (hF : IsTimeChangeClock (F b))
    (hadd : ∀ s, F (ContinuousPath.shift δ b) s = F b (δ + s) - F b δ) {η : ℝ}
    (hosc : ∀ r ≤ δ, ‖b r - b δ‖ ≤ η) :
    localUniformDist (lbmContinuousPath F b)
      (pathDelay (F b δ).toNNReal (lbmContinuousPath F (ContinuousPath.shift δ b))) ≤ η :=
  localUniformDist_le_of_forall_norm_le _ _ ((norm_nonneg _).trans (hosc δ le_rfl))
    (norm_lbmContinuousPath_sub_pathDelay_le hF hadd hosc)

end Path

section ApproxClock

variable {γ : ℝ} {hε : ℝ → ℂ → ℝ} {n : ℕ}

/-- **Additivity of the approximating LQG clock with drift.** For circle averages continuous at
the scale `2^{-n}`, `A_n(b, δ + s) = A_n(b, δ) + A_n(θ_δ b, s)` for every path `b`. -/
theorem lqgApproxClockPlus_add_eq_add_shift (hcont : Continuous (hε (dyadicScale n)))
    (b : ContinuousPath ℂ) (δ s : ℝ≥0) :
    lqgApproxClockPlus γ hε n b (δ + s) =
      lqgApproxClockPlus γ hε n b δ + lqgApproxClockPlus γ hε n (ContinuousPath.shift δ b) s := by
  unfold lqgApproxClockPlus
  rw [lqgClockApprox_add_eq_add_shift hcont b δ s, NNReal.coe_add]
  ring

/-- The approximating clock of the shifted path is the increment of the clock after `δ`. -/
theorem lqgApproxClockPlus_shift_eq_sub (hcont : Continuous (hε (dyadicScale n)))
    (b : ContinuousPath ℂ) (δ s : ℝ≥0) :
    lqgApproxClockPlus γ hε n (ContinuousPath.shift δ b) s =
      lqgApproxClockPlus γ hε n b (δ + s) - lqgApproxClockPlus γ hε n b δ := by
  rw [lqgApproxClockPlus_add_eq_add_shift hcont b δ s]
  ring

/-- **The approximate Liouville Brownian path restarted at `δ`.** After the clock value
`c = A_n(b, δ)`, the time-changed path of `b` is the time-changed path of `θ_δ b`. -/
theorem lbmContinuousPath_lqgApproxClockPlus_clockValue_add
    (hcont : Continuous (hε (dyadicScale n))) (b : ContinuousPath ℂ) (δ u : ℝ≥0) :
    lbmContinuousPath (lqgApproxClockPlus γ hε n) b
        ((lqgApproxClockPlus γ hε n b δ).toNNReal + u) =
      lbmContinuousPath (lqgApproxClockPlus γ hε n) (ContinuousPath.shift δ b) u :=
  lbmContinuousPath_clockValue_add (isTimeChangeClock_lqgApproxClockPlus hcont b)
    (lqgApproxClockPlus_shift_eq_sub hcont b δ) u

/-- The approximate Liouville Brownian path of `b` and the delayed approximate path of `θ_δ b`
are within the oscillation of `b` on `[0, δ]` in the local uniform distance. -/
theorem localUniformDist_lbmContinuousPath_lqgApproxClockPlus_pathDelay_le
    (hcont : Continuous (hε (dyadicScale n))) (b : ContinuousPath ℂ) (δ : ℝ≥0) {η : ℝ}
    (hosc : ∀ r ≤ δ, ‖b r - b δ‖ ≤ η) :
    localUniformDist (lbmContinuousPath (lqgApproxClockPlus γ hε n) b)
      (pathDelay (lqgApproxClockPlus γ hε n b δ).toNNReal
        (lbmContinuousPath (lqgApproxClockPlus γ hε n) (ContinuousPath.shift δ b))) ≤ η :=
  localUniformDist_lbmContinuousPath_pathDelay_le (isTimeChangeClock_lqgApproxClockPlus hcont b)
    (lqgApproxClockPlus_shift_eq_sub hcont b δ) hosc

end ApproxClock

section Markov

/-- **Simple Markov property at a fixed time.** The law of the shifted path `θ_δ b` under planar
Brownian motion from `z` is planar Brownian motion started from the heat kernel at time `δ`. -/
theorem planarBrownianMotion_map_shift (z : ℂ) (δ : ℝ≥0) :
    (planarBrownianMotion z).map (ContinuousPath.shift δ) =
      planarBrownianMotion ∘ₘ planarHeatSemigroup δ z := by
  have h := congrArg (fun K => K z)
    (SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_map_shift
      planarHeatSemigroup isConservative_planarHeatSemigroup
      isFellerKernelSemigroup_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup δ)
  rw [ProbabilityTheory.Kernel.map_apply _ (ContinuousPath.measurable_shift_fixed δ) z,
    ProbabilityTheory.Kernel.comp_apply] at h
  rw [planarBrownianMotion_eq_continuousProcess]
  exact h

/-- The laws of the shifted path `θ_δ b` under Brownian motion from two starting points are at
most as far apart in total variation as the heat kernels at time `δ`. -/
theorem tvDist_planarBrownianMotion_map_shift_le (z z' : ℂ) (δ : ℝ≥0) :
    QuantumZipper.TV.tvDist ((planarBrownianMotion z).map (ContinuousPath.shift δ))
        ((planarBrownianMotion z').map (ContinuousPath.shift δ)) ≤
      QuantumZipper.TV.tvDist (planarHeatSemigroup δ z) (planarHeatSemigroup δ z') := by
  rw [planarBrownianMotion_map_shift, planarBrownianMotion_map_shift]
  exact LatticeProb.tvDist_comp_le _ _ _

end Markov

end MatedCRT.FirstPass.Derived
