import MatedCRT.FirstPass.Derived.RevuzTimeChangeSemigroup
import MatedCRT.FirstPass.Derived.RevuzExcessiveBound

/-!
# The time-changed occupation before time `N` after the strong Markov property at `τ_r`

Let `A` be a positive continuous additive functional of planar Brownian motion with a good clock, with right
inverse `τ_v = inf {t | v < A_t}`, rational-time regularization `Ā` and time-changed position
`Ȳ_u = B_{τ̄_u}` computed with the right inverse `τ̄` of `Ā`. For a level shift `u`, a horizon `N` and a Borel set
`S` put `H(t, ω') = 1{t + τ̄_u(ω') ≤ N} 1_S(Ȳ_u(ω'))`. Then for every start `z`,
`E_z ∫_{r > 0} 1{τ_{r+u} ≤ N} 1_S(B_{τ_{r+u}}) dr = E_z ∫_{r > 0} E_{B_{τ_r}}[H(τ_r, ·)] dr`.

For each level `r`, almost surely `τ_{r+u} = τ_r + τ̄_u ∘ θ_{τ_r}` and `B_{τ_{r+u}} = Ȳ_u ∘ θ_{τ_r}`, so the
integrand on the left is `H(τ_r, θ_{τ_r} ω)`; the strong Markov property at `τ_r`, integrated in the level, gives
the right side (Revuz–Yor (1999), Chapter X, §1; Fukushima–Oshima–Takeda (2011), §6.2). Since the raw clock
need not be jointly measurable, the exchange of the level integral and the expectation is carried out on the
regularized clock, which agrees with the raw clock at every level along almost every unshifted path.

## Main results

* `horizonIntegrand`: the function `H` above, and `measurable_horizonIntegrand`;
* `lintegral_Ioi_clockInverse_add_eq_horizonIntegrand`: the identity above.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess

/-- The integrand `H(t, ω') = 1{t + τ̄_u(ω') ≤ N} 1_S(Ȳ_u(ω'))` that the time-changed occupation before time `N`
leaves after the strong Markov property at `τ_r`: `t` is the elapsed time `τ_r`, and `τ̄_u`, `Ȳ_u` are computed
with the regularized clock of the shifted path. -/
noncomputable def horizonIntegrand (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (u N : ℝ≥0) (S : Set ℂ)
    (p : ℝ≥0 × ContinuousPath ℂ) : ℝ≥0∞ :=
  (Iic N).indicator (1 : ℝ≥0 → ℝ≥0∞) (p.1 + clockInverse (regularize A) u p.2) *
    S.indicator (1 : ℂ → ℝ≥0∞) (timeChangeRegularized A u p.2)

theorem measurable_horizonIntegrand {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : ∀ t, Measurable (A t))
    (u N : ℝ≥0) {S : Set ℂ} (hS : MeasurableSet S) : Measurable (horizonIntegrand A u N S) := by
  have hτ : Measurable fun ω : ContinuousPath ℂ => clockInverse (regularize A) u ω :=
    (measurable_clockInverse_uncurry (measurable_regularize hA) (regularize_monotone A)).comp
      (measurable_const.prodMk measurable_id)
  have h1 : Measurable ((Iic N).indicator (1 : ℝ≥0 → ℝ≥0∞)) :=
    measurable_const.indicator measurableSet_Iic
  have h2 : Measurable (S.indicator (1 : ℂ → ℝ≥0∞)) := measurable_const.indicator hS
  exact (h1.comp (measurable_fst.add (hτ.comp measurable_snd))).mul
    (h2.comp ((measurable_timeChangeRegularized hA u).comp measurable_snd))

/-- The indicator of `{t ≤ N}` times `1_S(ω_t)`, written as a product. -/
theorem indicator_Iic_indicator_apply_eq_mul (N : ℝ≥0) (S : Set ℂ) (ω : ContinuousPath ℂ) (t : ℝ≥0) :
    (Iic N).indicator (fun t => S.indicator (1 : ℂ → ℝ≥0∞) (ω t)) t =
      (Iic N).indicator (1 : ℝ≥0 → ℝ≥0∞) t * S.indicator (1 : ℂ → ℝ≥0∞) (ω t) := by
  by_cases ht : t ∈ Iic N <;> simp [ht]

/-- **The time-changed occupation before time `N` after the strong Markov property at `τ_r`.** For a PCAF of
planar Brownian motion with a good clock, every start `z`, level shift `u`, horizon `N` and Borel set `S`,
`E_z ∫_{r > 0} 1{τ_{r+u} ≤ N} 1_S(B_{τ_{r+u}}) dr = E_z ∫_{r > 0} E_{B_{τ_r}}[H(τ_r, ·)] dr`
with `H = horizonIntegrand A u N S`. -/
theorem lintegral_Ioi_clockInverse_add_eq_horizonIntegrand {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) (z : ℂ) (u N : ℝ≥0) {S : Set ℂ}
    (hS : MeasurableSet S) :
    ∫⁻ ω, (∫⁻ r in Ioi (0 : ℝ), (Iic N).indicator (fun t => S.indicator (1 : ℂ → ℝ≥0∞) (ω t))
        (clockInverse A (r.toNNReal + u) ω)) ∂planarLaw z =
      ∫⁻ ω, (∫⁻ r in Ioi (0 : ℝ), ∫⁻ ω', horizonIntegrand A u N S (clockInverse A r.toNNReal ω, ω')
        ∂planarLaw (ω (clockInverse A r.toNNReal ω))) ∂planarLaw z := by
  have hH := measurable_horizonIntegrand hA.meas u N hS
  have hτ2 : Measurable fun p : ℝ≥0 × ContinuousPath ℂ => clockInverse (regularize A) p.1 p.2 :=
    measurable_clockInverse_uncurry (measurable_regularize hA.meas) (regularize_monotone A)
  have hτ' : Measurable fun p : ContinuousPath ℂ × ℝ =>
      clockInverse (regularize A) p.2.toNNReal p.1 :=
    hτ2.comp ((continuous_real_toNNReal.measurable.comp measurable_snd).prodMk measurable_fst)
  have hτu : Measurable fun p : ContinuousPath ℂ × ℝ =>
      clockInverse (regularize A) (p.2.toNNReal + u) p.1 :=
    hτ2.comp (((continuous_real_toNNReal.measurable.comp measurable_snd).add_const u).prodMk
      measurable_fst)
  have hI : Measurable ((Iic N).indicator (1 : ℝ≥0 → ℝ≥0∞)) :=
    measurable_const.indicator measurableSet_Iic
  have hJ : Measurable (S.indicator (1 : ℂ → ℝ≥0∞)) := measurable_const.indicator hS
  have hF : Measurable fun p : ContinuousPath ℂ × ℝ =>
      (Iic N).indicator (1 : ℝ≥0 → ℝ≥0∞) (clockInverse (regularize A) (p.2.toNNReal + u) p.1) *
        S.indicator (1 : ℂ → ℝ≥0∞) (p.1 (clockInverse (regularize A) (p.2.toNNReal + u) p.1)) :=
    (hI.comp hτu).mul (hJ.comp
      ((ContinuousEval.continuous_eval (F := ContinuousPath ℂ)).measurable.comp
        (measurable_fst.prodMk hτu)))
  have hL : Measurable fun p : ContinuousPath ℂ × ℝ =>
      horizonIntegrand A u N S (clockInverse (regularize A) p.2.toNNReal p.1,
        ContinuousPath.shift (clockInverse (regularize A) p.2.toNNReal p.1) p.1) :=
    hH.comp (hτ'.prodMk
      ((ContinuousPath.continuous_shift (alpha := ℂ)).measurable.comp (hτ'.prodMk measurable_fst)))
  have hreg := ae_clockInverse_regularize_eq hA z
  calc ∫⁻ ω, (∫⁻ r in Ioi (0 : ℝ), (Iic N).indicator (fun t => S.indicator (1 : ℂ → ℝ≥0∞) (ω t))
        (clockInverse A (r.toNNReal + u) ω)) ∂planarLaw z
      = ∫⁻ ω, (∫⁻ r in Ioi (0 : ℝ),
          (Iic N).indicator (1 : ℝ≥0 → ℝ≥0∞) (clockInverse (regularize A) (r.toNNReal + u) ω) *
            S.indicator (1 : ℂ → ℝ≥0∞) (ω (clockInverse (regularize A) (r.toNNReal + u) ω)))
          ∂planarLaw z := by
        refine lintegral_congr_ae ?_
        filter_upwards [hreg] with ω h
        refine lintegral_congr fun r => ?_
        simp only [h]
        exact indicator_Iic_indicator_apply_eq_mul N S ω _
    _ = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ ω,
          (Iic N).indicator (1 : ℝ≥0 → ℝ≥0∞) (clockInverse (regularize A) (r.toNNReal + u) ω) *
            S.indicator (1 : ℂ → ℝ≥0∞) (ω (clockInverse (regularize A) (r.toNNReal + u) ω))
          ∂planarLaw z :=
        lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ ω, horizonIntegrand A u N S (clockInverse (regularize A) r.toNNReal ω,
          ContinuousPath.shift (clockInverse (regularize A) r.toNNReal ω) ω) ∂planarLaw z := by
        refine lintegral_congr fun r => lintegral_congr_ae ?_
        filter_upwards [hreg, ae_clockInverse_add_eq_shift hA hG z r.toNNReal,
          ae_eval_clockInverse_add_eq_shift hA hG z r.toNNReal] with ω h h1 h2
        simp only [h]
        rw [h2 u, h1 u]
        rfl
    _ = ∫⁻ ω, (∫⁻ r in Ioi (0 : ℝ), horizonIntegrand A u N S (clockInverse (regularize A) r.toNNReal ω,
          ContinuousPath.shift (clockInverse (regularize A) r.toNNReal ω) ω)) ∂planarLaw z :=
        (lintegral_lintegral_swap hL.aemeasurable).symm
    _ = ∫⁻ ω, (∫⁻ r in Ioi (0 : ℝ), horizonIntegrand A u N S (clockInverse A r.toNNReal ω,
          ContinuousPath.shift (clockInverse A r.toNNReal ω) ω)) ∂planarLaw z := by
        refine lintegral_congr_ae ?_
        filter_upwards [hreg] with ω h
        simp only [h]
    _ = _ := lintegral_lintegral_shift_clockInverse_eq hA hG z (volume.restrict (Ioi 0)) hH

end MatedCRT
