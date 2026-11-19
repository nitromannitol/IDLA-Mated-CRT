import MatedCRT.FirstPass.Derived.RevuzTimeDependentFormula
import MatedCRT.FirstPass.Derived.RevuzClockInverseIntegral
import MatedCRT.FirstPass.Derived.RevuzMarkovAgainstClock

/-!
# The time-changed occupation before time `N` is at most `N` times the Revuz mass

For a positive continuous additive functional `A` of planar Brownian motion with a good clock, with right inverse
`τ_v = inf {t | v < A_t}` and time-changed path `Y_v = B_{τ_v}`, every level shift `u`, horizon `N` and Borel set `S`,
`∫ dz E_z ∫_{r > 0} 1{τ_{r+u} ≤ N} 1_S(Y_{r+u}) dr ≤ N · μ_A(S)`.

Pathwise, along a good path, `τ_{r+u} ≤ N` forces `r + u ≤ A_N`, so after the translation `v = r + u` the left
side is at most `∫_{(0, A_N]} 1_S(Y_v) dv = ∫_{(0,N]} 1_S(B_s) dA_s`; the expectation of the latter under the
Lebesgue-started motion is `N · μ_A(S)` by the window formula. This is the upper half of the excessiveness of the
Revuz measure for the time change (Azéma–Duflo–Revuz (1969), §2; Revuz–Yor (1999), Chapter X, §3).

## Main results

* `lintegral_Ioi_clockInverse_add_le`: the deterministic bound along a good path;
* `lintegral_lintegral_Ioi_clockInverse_add_le`: the Lebesgue-started bound by `N · μ_A(S)`.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess

/-- **The time-changed occupation before time `N`, pathwise.** Along a path where the clock starts at `0`, is
continuous, strictly increasing and unbounded, for every level shift `u`, horizon `N` and set `S`,
`∫_{r > 0} 1{τ_{r+u} ≤ N} 1_S(ω_{τ_{r+u}}) dr ≤ ∫_{(0, A_N]} 1_S(ω_{τ_r}) dr`. -/
theorem lintegral_Ioi_clockInverse_add_le {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {ω : ContinuousPath ℂ}
    (h0 : A 0 ω = 0) (hc : Continuous fun t => A t ω) (hs : StrictMono fun t => A t ω)
    (hu : Tendsto (fun t => A t ω) atTop atTop) (u N : ℝ≥0) (S : Set ℂ) :
    ∫⁻ r in Ioi (0 : ℝ), (Iic N).indicator (fun t => S.indicator (1 : ℂ → ℝ≥0∞) (ω t))
        (clockInverse A (r.toNNReal + u) ω) ≤
      ∫⁻ r in Ioc (0 : ℝ) (A N ω), S.indicator (1 : ℂ → ℝ≥0∞) (ω (clockInverse A r.toNNReal ω)) := by
  have hpt : ∀ r ∈ Ioi (0 : ℝ),
      (Iic N).indicator (fun t => S.indicator (1 : ℂ → ℝ≥0∞) (ω t)) (clockInverse A (r.toNNReal + u) ω) ≤
        (Ioc (0 : ℝ) (A N ω)).indicator
          (fun v => S.indicator (1 : ℂ → ℝ≥0∞) (ω (clockInverse A v.toNNReal ω))) (r + u) := by
    intro r hr
    by_cases hτ : clockInverse A (r.toNNReal + u) ω ∈ Iic N
    · have hle : r.toNNReal + u ≤ A N ω :=
        (clockInverse_le_iff_le_clock h0 hc hs (hu.eventually_gt_atTop _).exists).1 hτ
      have hcoe : ((r.toNNReal + u : ℝ≥0) : ℝ) = r + u := by
        rw [NNReal.coe_add, Real.coe_toNNReal r (le_of_lt hr)]
      have hmem : r + (u : ℝ) ∈ Ioc (0 : ℝ) (A N ω) := by
        refine ⟨add_pos_of_pos_of_nonneg hr u.coe_nonneg, ?_⟩
        have h := NNReal.coe_le_coe.2 hle
        rwa [hcoe] at h
      rw [indicator_of_mem hτ, indicator_of_mem hmem, ← hcoe, Real.toNNReal_coe]
    · rw [indicator_of_notMem hτ]
      exact bot_le
  calc ∫⁻ r in Ioi (0 : ℝ), (Iic N).indicator (fun t => S.indicator (1 : ℂ → ℝ≥0∞) (ω t))
          (clockInverse A (r.toNNReal + u) ω)
      ≤ ∫⁻ r in Ioi (0 : ℝ), (Ioc (0 : ℝ) (A N ω)).indicator
          (fun v => S.indicator (1 : ℂ → ℝ≥0∞) (ω (clockInverse A v.toNNReal ω))) (r + u) :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hpt))
    _ ≤ ∫⁻ r, (Ioc (0 : ℝ) (A N ω)).indicator
          (fun v => S.indicator (1 : ℂ → ℝ≥0∞) (ω (clockInverse A v.toNNReal ω))) (r + u) :=
        setLIntegral_le_lintegral _ _
    _ = ∫⁻ v, (Ioc (0 : ℝ) (A N ω)).indicator
          (fun v => S.indicator (1 : ℂ → ℝ≥0∞) (ω (clockInverse A v.toNNReal ω))) v :=
        lintegral_add_right_eq_self _ (u : ℝ)
    _ = ∫⁻ r in Ioc (0 : ℝ) (A N ω), S.indicator (1 : ℂ → ℝ≥0∞) (ω (clockInverse A r.toNNReal ω)) :=
        lintegral_indicator measurableSet_Ioc _

/-- **The time-changed occupation before time `N` is at most `N · μ_A(S)`.** For a positive continuous additive
functional `A` of planar Brownian motion with a good clock, every level shift `u`, horizon `N` and Borel set `S`,
`∫ dz E_z ∫_{r > 0} 1{τ_{r+u} ≤ N} 1_S(B_{τ_{r+u}}) dr ≤ N · μ_A(S)`. -/
theorem lintegral_lintegral_Ioi_clockInverse_add_le {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) (u N : ℝ≥0) {S : Set ℂ} (hS : MeasurableSet S) :
    ∫⁻ z, ∫⁻ ω, (∫⁻ r in Ioi (0 : ℝ), (Iic N).indicator (fun t => S.indicator (1 : ℂ → ℝ≥0∞) (ω t))
        (clockInverse A (r.toNNReal + u) ω)) ∂planarLaw z ≤ (N : ℝ≥0∞) * revuz planarLaw A S := by
  have hg : Measurable (S.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator hS
  calc ∫⁻ z, ∫⁻ ω, (∫⁻ r in Ioi (0 : ℝ), (Iic N).indicator (fun t => S.indicator (1 : ℂ → ℝ≥0∞) (ω t))
          (clockInverse A (r.toNNReal + u) ω)) ∂planarLaw z
      ≤ ∫⁻ z, ∫⁻ ω, ∫⁻ s in Ioc (0 : ℝ) N, S.indicator (1 : ℂ → ℝ≥0∞) (ω s.toNNReal)
          ∂(stieltjesOfNNReal fun v => regularize A v ω).measure ∂planarLaw z := by
        refine lintegral_mono fun z => lintegral_mono_ae ?_
        filter_upwards [hA.path z, hG z, ae_setLIntegral_regularize_Ioc_eq_clockInverse hA hG z N hg]
          with ω hp hgd hL
        rw [hL]
        exact lintegral_Ioi_clockInverse_add_le hp.1 hp.2.1 hgd.1 hgd.2 u N S
    _ = ENNReal.ofReal ((N : ℝ) - 0) * ∫⁻ y, S.indicator (1 : ℂ → ℝ≥0∞) y ∂revuz planarLaw A :=
        lintegral_setLIntegral_Ioc_regularize_eq hA le_rfl N hg
    _ = (N : ℝ≥0∞) * revuz planarLaw A S := by
        rw [sub_zero, ENNReal.ofReal_coe_nnreal, lintegral_indicator_one hS]

end MatedCRT
