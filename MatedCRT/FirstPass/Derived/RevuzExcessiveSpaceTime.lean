import MatedCRT.FirstPass.Derived.RevuzExcessiveMarkov
import MatedCRT.FirstPass.Derived.RevuzClockInverseIntegral
import MatedCRT.FirstPass.Derived.RevuzTimeDependentFormula

/-!
# The Revuz measure integrates the truncated time-changed hitting weight below `N` times its mass

Let `A` be a positive continuous additive functional of planar Brownian motion with a good clock and Revuz measure
`μ_A`, with right inverse `τ_v = inf {t | v < A_t}`, rational-time regularization `Ā`, right inverse `τ̄` of `Ā` and
time-changed position `Ȳ_u = B_{τ̄_u}`. For every level shift `u`, horizon `N` and Borel set `S`,
`∫ μ_A(dy) E_y[(N − τ̄_u)⁺ 1_S(Ȳ_u)] ≤ N · μ_A(S)`.

With `ψ(t, y) = E_y[1{t + τ̄_u ≤ N} 1_S(Ȳ_u)]`:
* along a good path, `ψ(t, ·) = 0` for `t > N` and `τ_r ≤ N ↔ r ≤ A_N`, so the change of variables `s = τ_r`
  turns `∫_{r > 0} ψ(τ_r, B_{τ_r}) dr` into `∫_{(0,N]} ψ(s, B_s) dA_s`;
* the time-dependent Revuz formula gives `∫ dz E_z ∫_{(0,N]} ψ(s, B_s) dA_s = ∫_{(0,N]} ∫ ψ(s, y) μ_A(dy) ds`, and
  Tonelli with `∫_{(0,N]} 1{s + c ≤ N} ds = (N − c)⁺` gives the left side above;
* the strong Markov step at `τ_r` and the bound by `N · μ_A(S)` of the time-changed occupation before `N` close the
  chain.
This is the integrated form of the excessiveness of the Revuz measure for the time change (Azéma–Duflo–Revuz
(1969), §2; Revuz–Yor (1999), Chapter X, §3).

## Main results

* `horizonExpectation`, `measurable_horizonExpectation`;
* `lintegral_Ioi_horizonExpectation_eq`: the change of variables along a good path;
* `setLIntegral_horizonIntegrand_eq`: `∫_{(0,N]} H(s, ω') ds = (N − τ̄_u ω')⁺ 1_S(Ȳ_u ω')`;
* `lintegral_revuz_truncatedHitting_le`: the bound above.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess _root_.HarmonicBalls

/-- `ψ(t, y) = E_y[H(t, ·)]` for the integrand `H = horizonIntegrand A u N S`. -/
noncomputable def horizonExpectation (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (u N : ℝ≥0) (S : Set ℂ)
    (p : ℝ≥0 × ℂ) : ℝ≥0∞ :=
  ∫⁻ ω', horizonIntegrand A u N S (p.1, ω') ∂planarLaw p.2

theorem measurable_horizonExpectation {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : ∀ t, Measurable (A t))
    (u N : ℝ≥0) {S : Set ℂ} (hS : MeasurableSet S) : Measurable (horizonExpectation A u N S) := by
  have hH := measurable_horizonIntegrand hA u N hS
  have h := (hH.comp (measurable_fst.fst.prodMk measurable_snd)).lintegral_kernel_prod_right'
    (κ := Kernel.comap planarBrownianMotion Prod.snd measurable_snd)
  simp only [Kernel.comap_apply] at h
  exact h

/-- `ψ(t, ·) = 0` after the horizon. -/
theorem horizonExpectation_eq_zero_of_lt {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {u N t : ℝ≥0} (S : Set ℂ)
    (ht : N < t) (y : ℂ) : horizonExpectation A u N S (t, y) = 0 := by
  unfold horizonExpectation
  refine lintegral_eq_zero_of_ae_eq_zero (Eventually.of_forall fun ω' => ?_)
  have hN : t + clockInverse (regularize A) u ω' ∉ Iic N := fun h =>
    absurd (ht.trans_le le_self_add) (not_lt.2 h)
  simp only [horizonIntegrand, indicator_of_notMem hN, zero_mul, Pi.zero_apply]

/-- **The change of variables `s = τ_r` for `ψ`.** Along a path where the clock starts at `0`, is continuous,
strictly increasing and unbounded, `∫_{r > 0} ψ(τ_r, ω_{τ_r}) dr = ∫_{(0,N]} ψ(s, ω_s) dA_s`. -/
theorem lintegral_Ioi_horizonExpectation_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : ∀ t, Measurable (A t))
    {ω : ContinuousPath ℂ} (h0 : A 0 ω = 0) (hc : Continuous fun t => A t ω) (hs : StrictMono fun t => A t ω)
    (hu : Tendsto (fun t => A t ω) atTop atTop) (u N : ℝ≥0) {S : Set ℂ} (hS : MeasurableSet S) :
    ∫⁻ r in Ioi (0 : ℝ), horizonExpectation A u N S
        (clockInverse A r.toNNReal ω, ω (clockInverse A r.toNNReal ω)) =
      ∫⁻ s in Ioc (0 : ℝ) N, horizonExpectation A u N S (s.toNNReal, ω s.toNNReal)
        ∂(stieltjesOfNNReal fun t => A t ω).measure := by
  have hψ := measurable_horizonExpectation hA u N hS
  have hF : Measurable fun s : ℝ => horizonExpectation A u N S (s.toNNReal, ω s.toNNReal) :=
    hψ.comp (continuous_real_toNNReal.measurable.prodMk
      (ω.continuous.comp continuous_real_toNNReal).measurable)
  rw [setLIntegral_stieltjes_clock_Ioc_eq_clockInverse hc hs hu hF]
  simp only [Real.toNNReal_zero, h0, NNReal.coe_zero, Real.toNNReal_coe]
  have hind : ∀ r : ℝ, horizonExpectation A u N S
      (clockInverse A r.toNNReal ω, ω (clockInverse A r.toNNReal ω)) =
      (Iic (A N ω : ℝ)).indicator (fun r => horizonExpectation A u N S
        (clockInverse A r.toNNReal ω, ω (clockInverse A r.toNNReal ω))) r := by
    intro r
    by_cases hr : r ∈ Iic (A N ω : ℝ)
    · rw [indicator_of_mem hr]
    · rw [indicator_of_notMem hr]
      have hlt : A N ω < r.toNNReal := Real.lt_toNNReal_iff_coe_lt.2 (not_le.1 hr)
      have hne : ∃ t, r.toNNReal < A t ω := (hu.eventually_gt_atTop r.toNNReal).exists
      have hτ : N < clockInverse A r.toNNReal ω :=
        not_le.1 fun h => absurd ((clockInverse_le_iff_le_clock h0 hc hs hne).1 h) (not_le.2 hlt)
      exact horizonExpectation_eq_zero_of_lt S hτ _
  refine (lintegral_congr hind).trans ?_
  rw [setLIntegral_indicator measurableSet_Iic, Iic_inter_Ioi]

/-- **The level integral of `H`.** `∫_{(0,N]} H(s, ω') ds = (N − τ̄_u ω')⁺ 1_S(Ȳ_u ω')`. -/
theorem setLIntegral_horizonIntegrand_eq (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (u N : ℝ≥0) (S : Set ℂ)
    (ω' : ContinuousPath ℂ) :
    ∫⁻ s in Ioc (0 : ℝ) N, horizonIntegrand A u N S (s.toNNReal, ω') =
      ENNReal.ofReal ((N : ℝ) - clockInverse (regularize A) u ω') *
        S.indicator (1 : ℂ → ℝ≥0∞) (timeChangeRegularized A u ω') := by
  simp only [horizonIntegrand]
  generalize clockInverse (regularize A) u ω' = c
  generalize S.indicator (1 : ℂ → ℝ≥0∞) (timeChangeRegularized A u ω') = J
  have hm : Measurable fun s : ℝ => (Iic N).indicator (1 : ℝ≥0 → ℝ≥0∞) (s.toNNReal + c) :=
    (measurable_const.indicator measurableSet_Iic).comp (continuous_real_toNNReal.measurable.add_const c)
  rw [lintegral_mul_const _ hm]
  congr 1
  have hpt : ∀ s ∈ Ioc (0 : ℝ) N, (Iic N).indicator (1 : ℝ≥0 → ℝ≥0∞) (s.toNNReal + c) =
      (Iic ((N : ℝ) - c)).indicator 1 s := by
    intro s hs
    have hiff : s.toNNReal + c ∈ Iic N ↔ s ∈ Iic ((N : ℝ) - c) := by
      simp only [mem_Iic, le_sub_iff_add_le, ← NNReal.coe_le_coe, NNReal.coe_add,
        Real.coe_toNNReal _ hs.1.le]
    by_cases h : s ∈ Iic ((N : ℝ) - c)
    · simp only [indicator_of_mem (hiff.2 h), indicator_of_mem h, Pi.one_apply]
    · simp only [indicator_of_notMem (mt hiff.1 h), indicator_of_notMem h]
  rw [setLIntegral_congr_fun measurableSet_Ioc hpt, lintegral_indicator_one measurableSet_Iic,
    Measure.restrict_apply measurableSet_Iic]
  have hset : Iic ((N : ℝ) - c) ∩ Ioc 0 N = Ioc 0 ((N : ℝ) - c) := by
    ext s
    simp only [mem_inter_iff, mem_Iic, mem_Ioc]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩
      exact ⟨h1, h2, h1.trans (sub_le_self _ c.coe_nonneg)⟩
  rw [hset, Real.volume_Ioc, sub_zero]

/-- **The Revuz measure integrates the truncated time-changed weight below `N` times its mass.** For a PCAF of
planar Brownian motion with a good clock and Revuz measure `μ_A`, every level shift `u`, horizon `N` and Borel set
`S`, `∫ μ_A(dy) E_y[(N − τ̄_u)⁺ 1_S(Ȳ_u)] ≤ N · μ_A(S)`. -/
theorem lintegral_revuz_truncatedHitting_le {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) (u N : ℝ≥0) {S : Set ℂ} (hS : MeasurableSet S) :
    ∫⁻ y, ∫⁻ ω', ENNReal.ofReal ((N : ℝ) - clockInverse (regularize A) u ω') *
        S.indicator (1 : ℂ → ℝ≥0∞) (timeChangeRegularized A u ω') ∂planarLaw y ∂revuz planarLaw A ≤
      (N : ℝ≥0∞) * revuz planarLaw A S := by
  have := sigmaFinite_revuz hA hG
  have hH := measurable_horizonIntegrand hA.meas u N hS
  have hψ := measurable_horizonExpectation hA.meas u N hS
  have hg : Measurable fun p : ℝ × ℂ => horizonExpectation A u N S (p.1.toNNReal, p.2) :=
    hψ.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)
  have hgs : Measurable fun p : ℂ × ℝ => horizonExpectation A u N S (p.2.toNNReal, p.1) :=
    hψ.comp ((continuous_real_toNNReal.measurable.comp measurable_snd).prodMk measurable_fst)
  have hsω : Measurable fun p : ContinuousPath ℂ × ℝ => horizonIntegrand A u N S (p.2.toNNReal, p.1) :=
    hH.comp ((continuous_real_toNNReal.measurable.comp measurable_snd).prodMk measurable_fst)
  calc ∫⁻ y, ∫⁻ ω', ENNReal.ofReal ((N : ℝ) - clockInverse (regularize A) u ω') *
        S.indicator (1 : ℂ → ℝ≥0∞) (timeChangeRegularized A u ω') ∂planarLaw y ∂revuz planarLaw A
      = ∫⁻ y, (∫⁻ s in Ioc (0 : ℝ) N, horizonExpectation A u N S (s.toNNReal, y)) ∂revuz planarLaw A := by
        refine lintegral_congr fun y => ?_
        exact (lintegral_congr fun ω' => (setLIntegral_horizonIntegrand_eq A u N S ω').symm).trans
          (lintegral_lintegral_swap hsω.aemeasurable)
    _ = ∫⁻ s in Ioc (0 : ℝ) N, ∫⁻ y, horizonExpectation A u N S (s.toNNReal, y) ∂revuz planarLaw A :=
        lintegral_lintegral_swap hgs.aemeasurable
    _ = ∫⁻ z, ∫⁻ ω, ∫⁻ s in Ioc (0 : ℝ) N, horizonExpectation A u N S (s.toNNReal, ω s.toNNReal)
          ∂(stieltjesOfNNReal fun t => A t ω).measure ∂planarLaw z :=
        (lintegral_setLIntegral_Ioc_spaceTime_eq hA hG (N : ℝ) hg).symm
    _ = ∫⁻ z, ∫⁻ ω, (∫⁻ r in Ioi (0 : ℝ), horizonExpectation A u N S
          (clockInverse A r.toNNReal ω, ω (clockInverse A r.toNNReal ω))) ∂planarLaw z := by
        refine lintegral_congr fun z => lintegral_congr_ae ?_
        filter_upwards [hA.path z, hG z] with ω hp hg'
        exact (lintegral_Ioi_horizonExpectation_eq hA.meas hp.1 hp.2.1 hg'.1 hg'.2 u N hS).symm
    _ = ∫⁻ z, ∫⁻ ω, (∫⁻ r in Ioi (0 : ℝ), (Iic N).indicator (fun t => S.indicator (1 : ℂ → ℝ≥0∞) (ω t))
          (clockInverse A (r.toNNReal + u) ω)) ∂planarLaw z :=
        lintegral_congr fun z =>
          (lintegral_Ioi_clockInverse_add_eq_horizonIntegrand hA hG z u N hS).symm
    _ ≤ (N : ℝ≥0∞) * revuz planarLaw A S := lintegral_lintegral_Ioi_clockInverse_add_le hA hG u N hS

end MatedCRT
