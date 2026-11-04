import MatedCRT.Proofs.Sec4.ConvergenceDivisible.LQGMeasureMeasurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.UrysohnsLemma

/-! # Measurability of compact-set LQG mass -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- LQG mass of a deterministic compact set has an almost-everywhere
measurable real-valued version. -/
theorem MatedCRTEnv.IsValid.aemeasurable_lqg_compact_mass
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {K : Set ℂ} (hK : IsCompact K) :
    AEMeasurable (fun ω => (S.μ ω K).toReal) S.P := by
  obtain ⟨f, hfK, _, hfc, hf01⟩ :=
    exists_continuous_one_zero_of_isCompact_of_isGδ hK hK.isClosed.isGδ
      isClosed_empty (disjoint_empty K)
  let F : ℕ → ℂ → ℝ := fun n x => f x ^ (n + 1)
  have hFc (n : ℕ) : Continuous (F n) := f.continuous.pow _
  have hFcompact (n : ℕ) : HasCompactSupport (F n) := by
    have h := hfc.mul_right (f' := fun x => f x ^ n)
    convert h using 1
    funext x
    simp [F, pow_succ, mul_comm]
  apply aemeasurable_of_tendsto_metrizable_ae atTop
    (f := fun n ω => ∫ x, F n x ∂S.μ ω)
  · intro n
    exact hS.aemeasurable_lqg_integral (F n) (hFc n) (hFcompact n)
  · filter_upwards [hS.isLQGMeasure] with ω hμ
    let _ : IsLocallyFiniteMeasure (S.μ ω) := hμ.isLocallyFiniteMeasure
    have hi : Integrable (fun x => f x) (S.μ ω) :=
      f.continuous.integrable_of_hasCompactSupport hfc
    have hlim : ∀ x, Tendsto (fun n => F n x) atTop
        (𝓝 (K.indicator (fun _ => (1 : ℝ)) x)) := by
      intro x
      by_cases hx : x ∈ K
      · have hfx : f x = 1 := by
          have := congrArg (fun s : Set ℂ => x ∈ s) hfK
          simpa using this.mp hx
        simp [F, hfx, hx]
      · have hne : f x ≠ 1 := by
          intro h
          apply hx
          rw [hfK]
          simpa using h
        have hlt : f x < 1 := lt_of_le_of_ne (hf01 x).2 hne
        have h := tendsto_pow_atTop_nhds_zero_of_lt_one (hf01 x).1 hlt
        have h' := h.mul_const (f x)
        simpa [F, pow_succ, hx] using h'
    have hb (n : ℕ) (x : ℂ) : ‖F n x‖ ≤ f x := by
      have hn : 0 ≤ f x := (hf01 x).1
      have hp : f x ^ n ≤ 1 := pow_le_one₀ hn (hf01 x).2
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hn _)]
      calc
        F n x = f x * f x ^ n := by simp [F, pow_succ, mul_comm]
        _ ≤ f x * 1 := mul_le_mul_of_nonneg_left hp hn
        _ = f x := mul_one _
    have hconv := tendsto_integral_of_dominated_convergence (fun x => f x)
      (fun n => (hFc n).aestronglyMeasurable) hi
      (fun n => Filter.Eventually.of_forall (hb n)) (Filter.Eventually.of_forall hlim)
    simpa [integral_indicator hK.isClosed.measurableSet, measureReal_def] using hconv

/-- The extended nonnegative LQG mass of a deterministic compact set is
almost-everywhere measurable. -/
theorem MatedCRTEnv.IsValid.aemeasurable_lqg_compact_mass_ennreal
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {K : Set ℂ} (hK : IsCompact K) :
    AEMeasurable (fun ω => S.μ ω K) S.P := by
  apply (hS.aemeasurable_lqg_compact_mass hK).ennreal_ofReal.congr
  filter_upwards [hS.isLQGMeasure] with ω hμ
  let _ : IsLocallyFiniteMeasure (S.μ ω) := hμ.isLocallyFiniteMeasure
  exact ENNReal.ofReal_toReal (hK.measure_lt_top.ne)

end MatedCRT
