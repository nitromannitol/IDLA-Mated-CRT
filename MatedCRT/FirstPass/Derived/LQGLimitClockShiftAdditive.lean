import MatedCRT.FirstPass.Derived.ConeReferenceClockMarkovTransfer
import LatticeProb.Prob.LimitAfterPositiveTimesShift

/-!
# Monotonicity and shift additivity of the limit LQG clock on the good set of paths

Let `A^k(b, t) = ∫_0^t ε_k^{γ²/2} e^{γ h_{ε_k}(b_s)} ds` be the approximating LQG clocks (Berestycki 2015, Section 2,
p. 6; `HarmonicBalls.lqgClockApprox`) at scales `ε_k ≥ 0` for a field whose circle averages `z ↦ h_{ε_k}(z)` are
continuous, and let `F(b) = LatticeProb.limitAfterPositiveTimes (A^·(b))` be the limit clock defined pathwise:
`F(b)_t = lim_m lim_k (A^k(b)_t - A^k(b)_{δ_m})` for `t > 0` and `F(b)_0 = 0`.

The good set of paths consists of the paths `b` for which (i) the increment limits `lim_k (A^k(b)_t - A^k(b)_{δ_m})`
exist for `δ_m ≤ t`, (ii) their limits as `m → ∞` exist at every `t > 0`, and (iii) `F(b)` is continuous. This is the
deterministic step R0(c) of the route to the divergence of the limit clock: on the good set,

* `F(b)` is nondecreasing (the approximating clocks are);
* `F(θ_s b)_t = F(b)_{s+t} - F(b)_s` for all `s, t ≥ 0`, where `θ_s b = b(s + ·)`, because
  `A^k(θ_s b)_t = A^k(b)_{s+t} - A^k(b)_s` exactly;
* the good set is invariant under every time shift `θ_s`.

Hence the almost sure monotonicity and shift additivity asked by the divergence criterion
`MatedCRT.KilledOccupation.planarBrownianMotion_ae_tendsto_atTop_of_additive` follow from the almost sure membership
in the good set, and its positivity at time `1/2` from strict monotonicity.

## Main statements

* `monotone_lqgClockApprox`: the approximating clock is nondecreasing in time.
* `lqgClockApprox_shift_eq_shiftIncrements`: the clocks of `θ_s b` are the increments after `s` of the clocks of `b`.
* `monotone_limitAfterPositiveTimes_lqgClockApprox`, `limitAfterPositiveTimes_lqgClockApprox_shift`: monotonicity and
  shift additivity of the limit clock on the good set.
* `exists_tendsto_lqgClockApprox_shift_sub_invSuccTime`, `exists_tendsto_incrementLimitAfter_lqgClockApprox_shift`,
  `continuous_limitAfterPositiveTimes_lqgClockApprox_shift`: invariance of the good set under time shifts.
* `ae_monotone_and_shift_limitAfterPositiveTimes_dyadic`: the almost sure form at the dyadic scales.
* `ae_ae_pos_limitAfterPositiveTimes_of_strictMono`: almost sure positivity at a positive time from strict
  monotonicity.
-/

open MeasureTheory Set Filter Topology HarmonicBalls MarkovProcess
open scoped NNReal

namespace MatedCRT.FirstPass.Derived.LQGLimitClockShift

/-- The approximating LQG clock at a nonnegative scale is nonnegative. -/
theorem lqgClockApprox_nonneg {γ ε : ℝ} (hε0 : 0 ≤ ε) (hε : ℝ → ℂ → ℝ) (b : ContinuousPath ℂ) (t : ℝ≥0) :
    0 ≤ lqgClockApprox γ hε ε b t :=
  intervalIntegral.integral_nonneg t.2 fun _ _ => mul_nonneg (Real.rpow_nonneg hε0 _) (Real.exp_pos _).le

/-- The approximating LQG clock at a nonnegative scale is nondecreasing in time, for continuous circle averages. -/
theorem monotone_lqgClockApprox {γ ε : ℝ} (hε0 : 0 ≤ ε) {hε : ℝ → ℂ → ℝ} (hcont : Continuous (hε ε))
    (b : ContinuousPath ℂ) : Monotone (lqgClockApprox γ hε ε b) := by
  intro t u htu
  obtain ⟨d, rfl⟩ : ∃ d, u = t + d := ⟨u - t, (add_tsub_cancel_of_le htu).symm⟩
  rw [lqgClockApprox_add_eq_add_shift hcont]
  exact le_add_of_nonneg_right (lqgClockApprox_nonneg hε0 _ _ _)

/-- **Clocks of the shifted path.** The approximating clocks of `θ_s b` are the increments after time `s` of the
approximating clocks of `b`: `A^k(θ_s b)_t = A^k(b)_{s+t} - A^k(b)_s`. -/
theorem lqgClockApprox_shift_eq_shiftIncrements {γ : ℝ} {r : ℕ → ℝ} {hε : ℝ → ℂ → ℝ}
    (hcont : ∀ k, Continuous (hε (r k))) (b : ContinuousPath ℂ) (s : ℝ≥0) :
    (fun k t => lqgClockApprox γ hε (r k) (ContinuousPath.shift s b) t) =
      LatticeProb.shiftIncrements (fun k t => lqgClockApprox γ hε (r k) b t) s := by
  funext k t
  rw [LatticeProb.shiftIncrements, lqgClockApprox_add_eq_add_shift (hcont k) b s t]
  ring

/-- **Monotonicity of the limit after positive times.** For nondecreasing approximants whose increment limits and
their limits as the base time decreases to `0` exist, the limit after positive times is nondecreasing. -/
theorem monotone_limitAfterPositiveTimes_of_tendsto {a : ℕ → ℝ≥0 → ℝ} (hmono : ∀ k, Monotone (a k))
    (hconv : ∀ m t, LatticeProb.invSuccTime m ≤ t →
      ∃ L, Tendsto (fun k => a k t - a k (LatticeProb.invSuccTime m)) atTop (𝓝 L))
    (hext : ∀ t, 0 < t → ∃ L, Tendsto (fun m => LatticeProb.incrementLimitAfter a m t) atTop (𝓝 L)) :
    Monotone (LatticeProb.limitAfterPositiveTimes a) := by
  have hnn : ∀ x, 0 < x → 0 ≤ LatticeProb.limitAfterPositiveTimes a x := by
    intro x hx
    obtain ⟨L, hL⟩ := hext x hx
    rw [LatticeProb.limitAfterPositiveTimes_of_ne_zero _ hx.ne', hL.limUnder_eq]
    obtain ⟨n, hn⟩ := LatticeProb.exists_invSuccTime_le hx
    refine ge_of_tendsto hL (eventually_atTop.2 ⟨n, fun m hm => ?_⟩)
    exact LatticeProb.incrementLimitAfter_nonneg hmono hconv
      ((LatticeProb.invSuccTime_antitone hm).trans hn)
  intro y x hyx
  rcases eq_zero_or_pos y with hy | hy
  · rw [hy, LatticeProb.limitAfterPositiveTimes_zero]
    rcases eq_zero_or_pos x with hx | hx
    · rw [hx, LatticeProb.limitAfterPositiveTimes_zero]
    · exact hnn x hx
  · have hlim := LatticeProb.tendsto_sub_limitAfterPositiveTimes hconv hext (hy.trans_le hyx) hy
    exact sub_nonneg.1 (ge_of_tendsto' hlim fun k => sub_nonneg.2 (hmono k hyx))

/-- **Monotonicity of the limit clock on the good set.** -/
theorem monotone_limitAfterPositiveTimes_lqgClockApprox {γ : ℝ} {r : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k)
    {hε : ℝ → ℂ → ℝ} (hcont : ∀ k, Continuous (hε (r k))) {b : ContinuousPath ℂ}
    (hconv : ∀ m t, LatticeProb.invSuccTime m ≤ t → ∃ L, Tendsto (fun k =>
      lqgClockApprox γ hε (r k) b t - lqgClockApprox γ hε (r k) b (LatticeProb.invSuccTime m)) atTop (𝓝 L))
    (hext : ∀ t, 0 < t → ∃ L, Tendsto (fun m => LatticeProb.incrementLimitAfter
      (fun k t => lqgClockApprox γ hε (r k) b t) m t) atTop (𝓝 L)) :
    Monotone (LatticeProb.limitAfterPositiveTimes fun k t => lqgClockApprox γ hε (r k) b t) :=
  monotone_limitAfterPositiveTimes_of_tendsto (fun k => monotone_lqgClockApprox (hr k) (hcont k) b) hconv hext

/-- **Shift additivity of the limit clock on the good set** (step R0(c)). If the increment limits of the
approximating clocks of `b` exist, their limits as the base time decreases to `0` exist, and the limit clock `F(b)` is
right-continuous at `s`, then `F(θ_s b)_t = F(b)_{s+t} - F(b)_s` for every `t`. -/
theorem limitAfterPositiveTimes_lqgClockApprox_shift {γ : ℝ} {r : ℕ → ℝ} {hε : ℝ → ℂ → ℝ}
    (hcont : ∀ k, Continuous (hε (r k))) {b : ContinuousPath ℂ}
    (hconv : ∀ m t, LatticeProb.invSuccTime m ≤ t → ∃ L, Tendsto (fun k =>
      lqgClockApprox γ hε (r k) b t - lqgClockApprox γ hε (r k) b (LatticeProb.invSuccTime m)) atTop (𝓝 L))
    (hext : ∀ t, 0 < t → ∃ L, Tendsto (fun m => LatticeProb.incrementLimitAfter
      (fun k t => lqgClockApprox γ hε (r k) b t) m t) atTop (𝓝 L))
    {s : ℝ≥0} (hrc : ContinuousWithinAt
      (LatticeProb.limitAfterPositiveTimes fun k t => lqgClockApprox γ hε (r k) b t) (Ioi s) s) (t : ℝ≥0) :
    LatticeProb.limitAfterPositiveTimes
        (fun k t => lqgClockApprox γ hε (r k) (ContinuousPath.shift s b) t) t =
      LatticeProb.limitAfterPositiveTimes (fun k t => lqgClockApprox γ hε (r k) b t) (s + t) -
        LatticeProb.limitAfterPositiveTimes (fun k t => lqgClockApprox γ hε (r k) b t) s := by
  rw [lqgClockApprox_shift_eq_shiftIncrements hcont b s]
  exact LatticeProb.limitAfterPositiveTimes_shiftIncrements hconv hext hrc t

/-- **Shift invariance of the good set, increment limits.** -/
theorem exists_tendsto_lqgClockApprox_shift_sub_invSuccTime {γ : ℝ} {r : ℕ → ℝ} {hε : ℝ → ℂ → ℝ}
    (hcont : ∀ k, Continuous (hε (r k))) {b : ContinuousPath ℂ}
    (hconv : ∀ m t, LatticeProb.invSuccTime m ≤ t → ∃ L, Tendsto (fun k =>
      lqgClockApprox γ hε (r k) b t - lqgClockApprox γ hε (r k) b (LatticeProb.invSuccTime m)) atTop (𝓝 L))
    (hext : ∀ t, 0 < t → ∃ L, Tendsto (fun m => LatticeProb.incrementLimitAfter
      (fun k t => lqgClockApprox γ hε (r k) b t) m t) atTop (𝓝 L)) (s : ℝ≥0) :
    ∀ m t, LatticeProb.invSuccTime m ≤ t → ∃ L, Tendsto (fun k =>
      lqgClockApprox γ hε (r k) (ContinuousPath.shift s b) t -
        lqgClockApprox γ hε (r k) (ContinuousPath.shift s b) (LatticeProb.invSuccTime m)) atTop (𝓝 L) := by
  have h := LatticeProb.exists_tendsto_shiftIncrements_sub_invSuccTime hconv hext s
  rw [← lqgClockApprox_shift_eq_shiftIncrements hcont b s] at h
  exact h

/-- **Shift invariance of the good set, outer limits.** -/
theorem exists_tendsto_incrementLimitAfter_lqgClockApprox_shift {γ : ℝ} {r : ℕ → ℝ} {hε : ℝ → ℂ → ℝ}
    (hcont : ∀ k, Continuous (hε (r k))) {b : ContinuousPath ℂ}
    (hconv : ∀ m t, LatticeProb.invSuccTime m ≤ t → ∃ L, Tendsto (fun k =>
      lqgClockApprox γ hε (r k) b t - lqgClockApprox γ hε (r k) b (LatticeProb.invSuccTime m)) atTop (𝓝 L))
    (hext : ∀ t, 0 < t → ∃ L, Tendsto (fun m => LatticeProb.incrementLimitAfter
      (fun k t => lqgClockApprox γ hε (r k) b t) m t) atTop (𝓝 L))
    {s : ℝ≥0} (hrc : ContinuousWithinAt
      (LatticeProb.limitAfterPositiveTimes fun k t => lqgClockApprox γ hε (r k) b t) (Ioi s) s) :
    ∀ t, 0 < t → ∃ L, Tendsto (fun m => LatticeProb.incrementLimitAfter
      (fun k t => lqgClockApprox γ hε (r k) (ContinuousPath.shift s b) t) m t) atTop (𝓝 L) := by
  rw [lqgClockApprox_shift_eq_shiftIncrements hcont b s]
  exact LatticeProb.exists_tendsto_incrementLimitAfter_shiftIncrements hconv hext hrc

/-- **Shift invariance of the good set, continuity.** -/
theorem continuous_limitAfterPositiveTimes_lqgClockApprox_shift {γ : ℝ} {r : ℕ → ℝ} {hε : ℝ → ℂ → ℝ}
    (hcont : ∀ k, Continuous (hε (r k))) {b : ContinuousPath ℂ}
    (hconv : ∀ m t, LatticeProb.invSuccTime m ≤ t → ∃ L, Tendsto (fun k =>
      lqgClockApprox γ hε (r k) b t - lqgClockApprox γ hε (r k) b (LatticeProb.invSuccTime m)) atTop (𝓝 L))
    (hext : ∀ t, 0 < t → ∃ L, Tendsto (fun m => LatticeProb.incrementLimitAfter
      (fun k t => lqgClockApprox γ hε (r k) b t) m t) atTop (𝓝 L))
    (hF : Continuous (LatticeProb.limitAfterPositiveTimes fun k t => lqgClockApprox γ hε (r k) b t)) (s : ℝ≥0) :
    Continuous (LatticeProb.limitAfterPositiveTimes
      fun k t => lqgClockApprox γ hε (r k) (ContinuousPath.shift s b) t) := by
  rw [lqgClockApprox_shift_eq_shiftIncrements hcont b s]
  exact LatticeProb.continuous_limitAfterPositiveTimes_shiftIncrements hconv hext hF s

/-- **Almost sure monotonicity and shift additivity of the dyadic limit clock.** For a field with continuous circle
averages at the dyadic scales `2^{-k}` and any law `μ` of paths, if `μ`-almost every path lies in the good set
(increment limits and their limits exist, and the limit clock is continuous), then `μ`-almost surely the limit clock
`F(b) = lim_m lim_k (A^k(b)_· - A^k(b)_{δ_m})` is nondecreasing and satisfies `F(θ_s b)_t = F(b)_{s+t} - F(b)_s` for
all `s, t`. This is the hypothesis `hadd` of `planarBrownianMotion_ae_tendsto_atTop_of_additive`. -/
theorem ae_monotone_and_shift_limitAfterPositiveTimes_dyadic {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    (hcont : ∀ k, Continuous (hε (HarmonicBalls.dyadicScale k))) {μ : Measure (ContinuousPath ℂ)}
    (hgood : ∀ᵐ b ∂μ,
      (∀ m t, LatticeProb.invSuccTime m ≤ t → ∃ L, Tendsto (fun k =>
        lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b t -
          lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b (LatticeProb.invSuccTime m)) atTop (𝓝 L)) ∧
      (∀ t, 0 < t → ∃ L, Tendsto (fun m => LatticeProb.incrementLimitAfter
        (fun k t => lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b t) m t) atTop (𝓝 L)) ∧
      Continuous (LatticeProb.limitAfterPositiveTimes
        fun k t => lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b t)) :
    ∀ᵐ b ∂μ,
      Monotone (LatticeProb.limitAfterPositiveTimes
        fun k t => lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b t) ∧
      ∀ s t, LatticeProb.limitAfterPositiveTimes
          (fun k t => lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) (ContinuousPath.shift s b) t) t =
        LatticeProb.limitAfterPositiveTimes
            (fun k t => lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b t) (s + t) -
          LatticeProb.limitAfterPositiveTimes
            (fun k t => lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b t) s := by
  filter_upwards [hgood] with b hb
  obtain ⟨hconv, hext, hF⟩ := hb
  exact ⟨monotone_limitAfterPositiveTimes_lqgClockApprox (fun k => (HarmonicBalls.dyadicScale_pos k).le)
      hcont hconv hext,
    fun s t => limitAfterPositiveTimes_lqgClockApprox_shift hcont hconv hext hF.continuousWithinAt t⟩

/-- **Almost sure positivity from strict monotonicity.** If, from Lebesgue-almost every start, a clock vanishing at
time `0` is almost surely strictly increasing, then it is almost surely positive at every positive time. This is the
hypothesis `hpos` of `planarBrownianMotion_ae_tendsto_atTop_of_additive` at `t = 1/2`. -/
theorem ae_ae_pos_limitAfterPositiveTimes_of_strictMono {Q : ℂ → Measure (ContinuousPath ℂ)}
    {a : ContinuousPath ℂ → ℕ → ℝ≥0 → ℝ}
    (hsm : ∀ᵐ w ∂(volume : Measure ℂ), ∀ᵐ b ∂(Q w), StrictMono (LatticeProb.limitAfterPositiveTimes (a b)))
    {t : ℝ≥0} (ht : 0 < t) :
    ∀ᵐ w ∂(volume : Measure ℂ), ∀ᵐ b ∂(Q w), 0 < LatticeProb.limitAfterPositiveTimes (a b) t := by
  filter_upwards [hsm] with w hw
  filter_upwards [hw] with b hb
  simpa using hb ht

end MatedCRT.FirstPass.Derived.LQGLimitClockShift
