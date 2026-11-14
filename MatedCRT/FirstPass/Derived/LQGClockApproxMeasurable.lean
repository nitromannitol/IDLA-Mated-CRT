import Mathlib
import HarmonicBalls.Defs.LBM

/-!
# Measurability of the approximating LQG clocks in the field, the path and the time

Let `X` be a measurable space of fields and `c : X → ℝ → ℂ → ℝ` a family of circle averages, `c x ε z = h_ε(z)` for
the field `x`. The approximating LQG clock (Berestycki 2015, Section 2, p. 6; `HarmonicBalls.lqgClockApprox`)
`A_ε(x, b, t) = ∫_0^t ε^{γ²/2} e^{γ h_ε(b_s)} ds`
of a continuous path `b` is a parametric integral of a jointly measurable integrand: the evaluation `(b, s) ↦ b_s` is
continuous on `ContinuousPath ℂ × ℝ` (Borel σ-algebra on `ContinuousPath ℂ`), so `(x, b, s) ↦ h_ε(b_s)` is measurable
as soon as the circle averages `(x, z) ↦ c x ε z` at the scale `ε` are jointly measurable. No continuity of
`z ↦ c x ε z` is used for measurability (the Bochner integral of a non-integrable integrand is `0`, and the parametric
integral is measurable in either case). Continuity in time uses only the local integrability of the integrand along
the path, which holds when `z ↦ c x ε z` is continuous.

## Main statements

* `measurable_lqgClockApprox_field_path_time`: `(x, b, t) ↦ A_ε(x, b, t)` is measurable on
  `X × ContinuousPath ℂ × ℝ≥0`.
* `measurable_lqgClockApprox_field`: `(x, b) ↦ A_ε(x, b, t)` is measurable for each time `t`.
* `continuous_lqgClockApprox_of_intervalIntegrable`, `continuous_lqgClockApprox_field`: `t ↦ A_ε(x, b, t)` is
  continuous when the integrand is locally integrable along `b`, in particular when `z ↦ c x ε z` is continuous.
* `measurable_lqgClockApprox_add_field`, `measurable_lqgClockApprox_add_field_path_time`,
  `continuous_lqgClockApprox_add_field`: the same three facts for the clock `A_ε(x, b, t) + ε t` with a linear drift.
-/

open MeasureTheory Set HarmonicBalls MarkovProcess
open scoped NNReal

namespace MatedCRT.LQGClockApproxMeasurable

/-- The integrand `ε^{γ²/2} e^{γ h_ε(b_s)}` of the approximating LQG clock is jointly measurable in the field `x`, the
path `b`, the time `t` (on which it does not depend) and the integration variable `s`, as soon as the circle averages
`(x, z) ↦ c x ε z` at the scale `ε` are jointly measurable. -/
theorem measurable_clockIntegrand {X : Type*} [MeasurableSpace X] {c : X → ℝ → ℂ → ℝ} (γ : ℝ) {ε : ℝ}
    (hcε : Measurable fun q : X × ℂ => c q.1 ε q.2) :
    Measurable fun y : (X × ContinuousPath ℂ × ℝ≥0) × ℝ =>
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * c y.1.1 ε (y.1.2.1 y.2.toNNReal)) := by
  have heval : Measurable fun y : (X × ContinuousPath ℂ × ℝ≥0) × ℝ => y.1.2.1 y.2.toNNReal := by
    have hcont : Continuous fun p : ContinuousPath ℂ × ℝ => p.1 p.2.toNNReal :=
      ContinuousEval.continuous_eval.comp
        (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))
    exact hcont.measurable.comp (measurable_fst.snd.fst.prodMk measurable_snd)
  exact measurable_const.mul (Real.continuous_exp.measurable.comp
    (measurable_const.mul (hcε.comp (measurable_fst.fst.prodMk heval))))

/-- **Joint measurability at one scale.** If the circle averages `(x, z) ↦ c x ε z` at the scale `ε` are jointly
measurable, then the approximating LQG clock `A_ε(x, b, t) = ∫_0^t ε^{γ²/2} e^{γ h_ε(b_s)} ds` is jointly measurable
in the field `x`, the path `b` and the time `t`. -/
theorem measurable_lqgClockApprox_field_path_time_of_scale {X : Type*} [MeasurableSpace X]
    {c : X → ℝ → ℂ → ℝ} (γ : ℝ) {ε : ℝ} (hcε : Measurable fun q : X × ℂ => c q.1 ε q.2) :
    Measurable fun p : X × ContinuousPath ℂ × ℝ≥0 => lqgClockApprox γ (c p.1) ε p.2.1 p.2.2 := by
  have hD : MeasurableSet {y : (X × ContinuousPath ℂ × ℝ≥0) × ℝ | y.2 ≤ (y.1.2.2 : ℝ)} :=
    measurableSet_le measurable_snd (measurable_coe_nnreal_real.comp measurable_fst.snd.snd)
  have hF : Measurable fun y : (X × ContinuousPath ℂ × ℝ≥0) × ℝ =>
      (Iic (y.1.2.2 : ℝ)).indicator
        (fun s => ε ^ (γ ^ 2 / 2) * Real.exp (γ * c y.1.1 ε (y.1.2.1 s.toNNReal))) y.2 := by
    have heq : (fun y : (X × ContinuousPath ℂ × ℝ≥0) × ℝ =>
        (Iic (y.1.2.2 : ℝ)).indicator
          (fun s => ε ^ (γ ^ 2 / 2) * Real.exp (γ * c y.1.1 ε (y.1.2.1 s.toNNReal))) y.2) =
        {y : (X × ContinuousPath ℂ × ℝ≥0) × ℝ | y.2 ≤ (y.1.2.2 : ℝ)}.indicator
          (fun y => ε ^ (γ ^ 2 / 2) * Real.exp (γ * c y.1.1 ε (y.1.2.1 y.2.toNNReal))) := by
      funext y
      by_cases hy : y.2 ≤ (y.1.2.2 : ℝ)
      · rw [Set.indicator_of_mem (show y.2 ∈ Iic (y.1.2.2 : ℝ) from hy),
          Set.indicator_of_mem
            (show y ∈ {w : (X × ContinuousPath ℂ × ℝ≥0) × ℝ | w.2 ≤ (w.1.2.2 : ℝ)} from hy)]
      · rw [Set.indicator_of_notMem (show y.2 ∉ Iic (y.1.2.2 : ℝ) from hy),
          Set.indicator_of_notMem
            (show y ∉ {w : (X × ContinuousPath ℂ × ℝ≥0) × ℝ | w.2 ≤ (w.1.2.2 : ℝ)} from hy)]
    rw [heq]
    exact (measurable_clockIntegrand γ hcε).indicator hD
  have hI := hF.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))
  have hfun : (fun p : X × ContinuousPath ℂ × ℝ≥0 => lqgClockApprox γ (c p.1) ε p.2.1 p.2.2) =
      fun p => ∫ s, (Iic (p.2.2 : ℝ)).indicator
        (fun s => ε ^ (γ ^ 2 / 2) * Real.exp (γ * c p.1 ε (p.2.1 s.toNNReal))) s
          ∂(volume.restrict (Ioi (0 : ℝ))) := by
    funext p
    show lqgClockApprox γ (c p.1) ε p.2.1 p.2.2 = _
    rw [lqgClockApprox, intervalIntegral.integral_of_le p.2.2.coe_nonneg,
      setIntegral_indicator measurableSet_Iic,
      show Ioi (0 : ℝ) ∩ Iic (p.2.2 : ℝ) = Ioc 0 (p.2.2 : ℝ) from rfl]
  rw [hfun]
  exact hI.measurable

/-- **Joint measurability in the field, the path and the time.** For circle averages `c` that are jointly measurable
in the field and the point at every scale, `(x, b, t) ↦ A_ε(x, b, t)` is measurable on `X × ContinuousPath ℂ × ℝ≥0`.
-/
theorem measurable_lqgClockApprox_field_path_time {X : Type*} [MeasurableSpace X] {c : X → ℝ → ℂ → ℝ}
    (hc : ∀ r, Measurable fun q : X × ℂ => c q.1 r q.2) (γ ε : ℝ) :
    Measurable fun p : X × ContinuousPath ℂ × ℝ≥0 => lqgClockApprox γ (c p.1) ε p.2.1 p.2.2 :=
  measurable_lqgClockApprox_field_path_time_of_scale γ (hc ε)

/-- **Measurability in the field and the path.** For circle averages `c` that are jointly measurable in the field and
the point at every scale, `(x, b) ↦ A_ε(x, b, t)` is measurable for every time `t`. -/
theorem measurable_lqgClockApprox_field {X : Type*} [MeasurableSpace X] {c : X → ℝ → ℂ → ℝ}
    (hc : ∀ r, Measurable fun q : X × ℂ => c q.1 r q.2) (γ ε : ℝ) (t : ℝ≥0) :
    Measurable fun p : X × ContinuousPath ℂ => lqgClockApprox γ (c p.1) ε p.2 t :=
  (measurable_lqgClockApprox_field_path_time hc γ ε).comp
    (measurable_fst.prodMk
      (measurable_snd.prodMk (measurable_const : Measurable fun _ : X × ContinuousPath ℂ => t)))

/-- **Continuity in time.** The approximating LQG clock of a path `b` is continuous in time whenever its integrand
`s ↦ ε^{γ²/2} e^{γ h_ε(b_s)}` is locally integrable on `ℝ`. -/
theorem continuous_lqgClockApprox_of_intervalIntegrable {γ ε : ℝ} {hε : ℝ → ℂ → ℝ} {b : ContinuousPath ℂ}
    (hint : ∀ u v : ℝ, IntervalIntegrable
      (fun s : ℝ => ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (b s.toNNReal))) volume u v) :
    Continuous fun t : ℝ≥0 => lqgClockApprox γ hε ε b t :=
  (intervalIntegral.continuous_primitive hint 0).comp NNReal.continuous_coe

/-- **Continuity in time for a continuous field.** If `z ↦ c x ε z` is continuous, then `t ↦ A_ε(x, b, t)` is
continuous for every continuous path `b`. -/
theorem continuous_lqgClockApprox_field {X : Type*} (c : X → ℝ → ℂ → ℝ) (γ ε : ℝ) (x : X)
    (hcont : Continuous (c x ε)) (b : ContinuousPath ℂ) :
    Continuous fun t : ℝ≥0 => lqgClockApprox γ (c x) ε b t := by
  have hd : Continuous fun s : ℝ => ε ^ (γ ^ 2 / 2) * Real.exp (γ * c x ε (b s.toNNReal)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      (hcont.comp (b.continuous.comp continuous_real_toNNReal))))
  exact continuous_lqgClockApprox_of_intervalIntegrable fun u v => hd.intervalIntegrable u v

/-- The clock `A_ε(x, b, t) + ε t` with a linear drift is measurable in the field and the path for every time `t`. -/
theorem measurable_lqgClockApprox_add_field {X : Type*} [MeasurableSpace X] {c : X → ℝ → ℂ → ℝ}
    (hc : ∀ r, Measurable fun q : X × ℂ => c q.1 r q.2) (γ ε : ℝ) (t : ℝ≥0) :
    Measurable fun p : X × ContinuousPath ℂ => lqgClockApprox γ (c p.1) ε p.2 t + ε * t :=
  (measurable_lqgClockApprox_field hc γ ε t).add_const _

/-- The clock `A_ε(x, b, t) + ε t` with a linear drift is jointly measurable in the field, the path and the time. -/
theorem measurable_lqgClockApprox_add_field_path_time {X : Type*} [MeasurableSpace X] {c : X → ℝ → ℂ → ℝ}
    (hc : ∀ r, Measurable fun q : X × ℂ => c q.1 r q.2) (γ ε : ℝ) :
    Measurable fun p : X × ContinuousPath ℂ × ℝ≥0 =>
      lqgClockApprox γ (c p.1) ε p.2.1 p.2.2 + ε * p.2.2 :=
  (measurable_lqgClockApprox_field_path_time hc γ ε).add
    (measurable_const.mul (measurable_coe_nnreal_real.comp measurable_snd.snd))

/-- The clock `A_ε(x, b, t) + ε t` with a linear drift is continuous in time if `z ↦ c x ε z` is continuous. -/
theorem continuous_lqgClockApprox_add_field {X : Type*} (c : X → ℝ → ℂ → ℝ) (γ ε : ℝ) (x : X)
    (hcont : Continuous (c x ε)) (b : ContinuousPath ℂ) :
    Continuous fun t : ℝ≥0 => lqgClockApprox γ (c x) ε b t + ε * t :=
  (continuous_lqgClockApprox_field c γ ε x hcont b).add (continuous_const.mul NNReal.continuous_coe)

end MatedCRT.LQGClockApproxMeasurable
