import MatedCRT.FirstPass.Closure.M0CdfMeasurable
import MatedCRT.FirstPass.Derived.LQGApproxPathKernel

/-!
# The Liouville Brownian motion path restarted at a deterministic time

Deterministic facts about the time change `t ↦ b (F⁻¹(t))` of a path `b` by a time-change clock
`F b` (`HarmonicBalls.liouvilleBrownianPath`). Fix `δ ≥ 0` and write `θ_δ b = b (δ + ·)`. When the
clock is additive at `δ`, that is `F (θ_δ b) s = F b (δ + s) - F b δ` (as the approximating LQG
clocks are, `lqgClockApprox_add_eq_add_shift`), then

* after the clock value `a = F b δ`, the time-changed path of `b` is the time-changed path of
  `θ_δ b`: `X (a + u) = X' u` (`liouvilleBrownianPath_clockValue_add`);
* uniformly on `[0, T]`, `‖X t - X' t‖` is at most the oscillation of `b` on `[0, δ]` plus the
  modulus of continuity of `X'` at the lag `a` (`norm_liouvilleBrownianPath_sub_restart_le`).

These are the deterministic steps in comparing Liouville Brownian motion from `z` with Liouville
Brownian motion started afresh, at time `δ`, from the Brownian position `b δ`.
-/

namespace MatedCRT.FirstPass.Derived

open MarkovProcess Filter
open _root_.HarmonicBalls
open scoped NNReal

/-- The clock inverse of a time-change clock is the unique preimage. -/
theorem clockInverse_eq_of_apply_eq {f : ℝ≥0 → ℝ} (hf : IsTimeChangeClock f) {t s : ℝ≥0}
    (h : f s = t) : clockInverse f t = s :=
  hf.strictMono.injective ((M0Cdf.apply_clockInverse hf t).trans h.symm)

/-- A time-change clock is nonnegative. -/
theorem isTimeChangeClock_nonneg {f : ℝ≥0 → ℝ} (hf : IsTimeChangeClock f) (s : ℝ≥0) :
    0 ≤ f s := by
  have h := hf.strictMono.monotone (zero_le : (0 : ℝ≥0) ≤ s)
  rwa [hf.map_zero] at h

/-- The clock restarted at the time `δ`, `s ↦ f (δ + s) - f δ`, is a time-change clock. -/
theorem isTimeChangeClock_restart {f : ℝ≥0 → ℝ} (hf : IsTimeChangeClock f) (δ : ℝ≥0) :
    IsTimeChangeClock (fun s => f (δ + s) - f δ) where
  map_zero := by simp
  continuous := (hf.continuous.comp (continuous_const.add continuous_id)).sub continuous_const
  strictMono := fun x y h => show f (δ + x) - f δ < f (δ + y) - f δ from
    sub_lt_sub_right (hf.strictMono (add_lt_add_of_le_of_lt (le_refl δ) h)) _
  tendsto_atTop := by
    have h1 : Tendsto (fun s : ℝ≥0 => f (δ + s)) atTop atTop :=
      hf.tendsto_atTop.comp (tendsto_atTop_mono (fun s => le_add_self) tendsto_id)
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-f δ) h1

/-- **Restart identity for the clock inverse.** After the clock value `f δ`, the inverse of `f` is
`δ` plus the inverse of the clock restarted at `δ`. -/
theorem clockInverse_clockValue_add {f : ℝ≥0 → ℝ} (hf : IsTimeChangeClock f) (δ u : ℝ≥0) :
    clockInverse f ((f δ).toNNReal + u) = δ + clockInverse (fun s => f (δ + s) - f δ) u := by
  apply clockInverse_eq_of_apply_eq hf
  have hg : f (δ + clockInverse (fun s => f (δ + s) - f δ) u) - f δ = u :=
    M0Cdf.apply_clockInverse (isTimeChangeClock_restart hf δ) u
  rw [NNReal.coe_add, Real.coe_toNNReal _ (isTimeChangeClock_nonneg hf δ)]
  linarith

section Path

variable {F : ContinuousPath ℂ → ℝ≥0 → ℝ} {b : ContinuousPath ℂ} {δ : ℝ≥0}

/-- Under clock additivity at `δ`, the clock of the shifted path is a time-change clock. -/
theorem isTimeChangeClock_shift (hF : IsTimeChangeClock (F b))
    (hadd : ∀ s, F (ContinuousPath.shift δ b) s = F b (δ + s) - F b δ) :
    IsTimeChangeClock (F (ContinuousPath.shift δ b)) := by
  rw [show F (ContinuousPath.shift δ b) = fun s => F b (δ + s) - F b δ from funext hadd]
  exact isTimeChangeClock_restart hF δ

/-- **The time-changed path after the clock value at `δ`.** Under clock additivity at `δ`, the
Liouville Brownian path of `b` at time `F b δ + u` is the Liouville Brownian path of `θ_δ b` at
time `u`. -/
theorem liouvilleBrownianPath_clockValue_add (hF : IsTimeChangeClock (F b))
    (hadd : ∀ s, F (ContinuousPath.shift δ b) s = F b (δ + s) - F b δ) (u : ℝ≥0) :
    liouvilleBrownianPath F b ((F b δ).toNNReal + u) =
      liouvilleBrownianPath F (ContinuousPath.shift δ b) u := by
  unfold liouvilleBrownianPath
  rw [show F (ContinuousPath.shift δ b) = fun s => F b (δ + s) - F b δ from funext hadd,
    clockInverse_clockValue_add hF δ u, ContinuousPath.shift_apply]

/-- Under clock additivity at `δ`, the Liouville Brownian path of `θ_δ b` starts at `b δ`. -/
theorem liouvilleBrownianPath_shift_zero (hF : IsTimeChangeClock (F b))
    (hadd : ∀ s, F (ContinuousPath.shift δ b) s = F b (δ + s) - F b δ) :
    liouvilleBrownianPath F (ContinuousPath.shift δ b) 0 = b δ := by
  have hG := isTimeChangeClock_shift hF hadd
  have h0 : clockInverse (F (ContinuousPath.shift δ b)) 0 = 0 :=
    clockInverse_eq_of_apply_eq hG (by rw [hG.map_zero]; rfl)
  rw [liouvilleBrownianPath, h0, ContinuousPath.shift_apply, add_zero]

/-- Before the clock value at `δ`, the time-changed path of `b` only uses `b` on `[0, δ]`. -/
theorem clockInverse_le_of_le_clockValue (hF : IsTimeChangeClock (F b)) {t : ℝ≥0}
    (ht : t ≤ (F b δ).toNNReal) : clockInverse (F b) t ≤ δ := by
  apply hF.strictMono.le_iff_le.mp
  rw [M0Cdf.apply_clockInverse hF t]
  exact (NNReal.coe_le_coe.mpr ht).trans (Real.coe_toNNReal _ (isTimeChangeClock_nonneg hF δ)).le

/-- **Uniform comparison with the path restarted at `δ`.** Under clock additivity at `δ`, if `b`
oscillates by at most `η` on `[0, δ]` (relative to `b δ`) and the Liouville Brownian path `X'` of
`θ_δ b` moves by at most `ε` over every time lag at most `F b δ` inside `[0, T]`, then the
Liouville Brownian paths `X` of `b` and `X'` of `θ_δ b` are within `η + ε` on `[0, T]`. -/
theorem norm_liouvilleBrownianPath_sub_restart_le (hF : IsTimeChangeClock (F b))
    (hadd : ∀ s, F (ContinuousPath.shift δ b) s = F b (δ + s) - F b δ) {T : ℝ≥0} {η ε : ℝ}
    (hosc : ∀ r ≤ δ, ‖b r - b δ‖ ≤ η)
    (hmod : ∀ u u' : ℝ≥0, u ≤ u' → u' ≤ u + (F b δ).toNNReal → u' ≤ T →
      ‖liouvilleBrownianPath F (ContinuousPath.shift δ b) u -
        liouvilleBrownianPath F (ContinuousPath.shift δ b) u'‖ ≤ ε)
    {t : ℝ≥0} (ht : t ≤ T) :
    ‖liouvilleBrownianPath F b t - liouvilleBrownianPath F (ContinuousPath.shift δ b) t‖ ≤
      η + ε := by
  have hη : 0 ≤ η := (norm_nonneg _).trans (hosc δ le_rfl)
  rcases le_total (F b δ).toNNReal t with hat | hta
  · obtain ⟨u, rfl⟩ : ∃ u, t = (F b δ).toNNReal + u :=
      ⟨t - (F b δ).toNNReal, (add_tsub_cancel_of_le hat).symm⟩
    rw [liouvilleBrownianPath_clockValue_add hF hadd u]
    have h := hmod u ((F b δ).toNNReal + u) le_add_self (add_comm _ _).le ht
    linarith
  · have h1 : ‖liouvilleBrownianPath F b t - b δ‖ ≤ η :=
      hosc _ (clockInverse_le_of_le_clockValue hF hta)
    have h2 := hmod 0 t (zero_le : (0 : ℝ≥0) ≤ t) (by simpa using hta) ht
    rw [liouvilleBrownianPath_shift_zero hF hadd] at h2
    calc ‖liouvilleBrownianPath F b t - liouvilleBrownianPath F (ContinuousPath.shift δ b) t‖
        ≤ ‖liouvilleBrownianPath F b t - b δ‖ +
            ‖b δ - liouvilleBrownianPath F (ContinuousPath.shift δ b) t‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ η + ε := add_le_add h1 h2

/-- The restart identity for `lbmContinuousPath`. -/
theorem lbmContinuousPath_clockValue_add (hF : IsTimeChangeClock (F b))
    (hadd : ∀ s, F (ContinuousPath.shift δ b) s = F b (δ + s) - F b δ) (u : ℝ≥0) :
    lbmContinuousPath F b ((F b δ).toNNReal + u) =
      lbmContinuousPath F (ContinuousPath.shift δ b) u := by
  rw [lbmContinuousPath_of_isTimeChangeClock hF,
    lbmContinuousPath_of_isTimeChangeClock (isTimeChangeClock_shift hF hadd)]
  exact liouvilleBrownianPath_clockValue_add hF hadd u

end Path

end MatedCRT.FirstPass.Derived
