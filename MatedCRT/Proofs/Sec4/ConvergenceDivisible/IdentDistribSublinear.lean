import MatedCRT.Proofs.Sec4.ConvergenceDivisible.RadialOscillationTransfer
import Mathlib.Probability.StrongLaw

/-! # Sublinear growth of identically distributed integrable variables -/

namespace MatedCRT

open Filter MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal NNReal

/-- A sequence of identically distributed nonnegative integrable random variables
is eventually bounded by any positive multiple of its index. Independence is
not needed: the integrable tail estimate and Borel--Cantelli suffice. -/
theorem ae_eventually_le_mul_of_identDistrib
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : Integrable (X 0) μ)
    (hpos : ∀ n ω, 0 ≤ X n ω)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    {a : ℝ} (ha : 0 < a) :
    ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, X n ω ≤ a * n := by
  let : MeasureSpace Ω := ⟨μ⟩
  let Y : ℕ → Ω → ℝ := fun n ω => X n ω / a
  have hy : Integrable (Y 0) μ := hX.div_const a
  have hypos : ∀ n, 0 ≤ Y n := fun n ω => div_nonneg (hpos n ω) ha.le
  have hyid : ∀ n, IdentDistrib (Y n) (Y 0) μ μ := by
    intro n
    exact (hid n).comp (measurable_id.div_const a)
  have hsum : (∑' n : ℕ, μ {ω | Y n ω ∈ Set.Ioi (n : ℝ)}) < ∞ := by
    convert! tsum_prob_mem_Ioi_lt_top hy (hypos 0) using 2
    ext1 n
    exact (hyid n).measure_mem_eq measurableSet_Ioi
  filter_upwards [ae_eventually_notMem hsum.ne] with ω hω
  filter_upwards [hω] with n hn
  have hbound : Y n ω ≤ n := le_of_not_gt hn
  simpa only [mul_comm] using (div_le_iff₀ ha).mp hbound

/-- An integrable stationary bound on Brownian unit-interval oscillations
implies the sublinear oscillation estimate needed for cone scaling. -/
theorem brownian_oscillation_of_identDistrib_bound
    (X : ℕ → ContinuousPath ℝ → ℝ)
    (hX : Integrable (X 0) (brownianMotion 0))
    (hpos : ∀ n w, 0 ≤ X n w)
    (hid : ∀ n, IdentDistrib (X n) (X 0) (brownianMotion 0) (brownianMotion 0))
    (hbound : ∀ (n : ℕ) w (t : ℝ≥0), (n : ℝ≥0) ≤ t → t ≤ (n : ℝ≥0) + 1 →
      |w t - w (n : ℝ≥0)| ≤ X n w)
    {a : ℝ} (ha : 0 < a) :
    ∀ᵐ w ∂brownianMotion 0, ∀ᶠ n : ℕ in atTop, ∀ t : ℝ≥0,
      (n : ℝ≥0) ≤ t → t ≤ (n : ℝ≥0) + 1 →
      |w t - w (n : ℝ≥0)| ≤ a * n := by
  filter_upwards [ae_eventually_le_mul_of_identDistrib X hX hpos hid ha] with w hw
  filter_upwards [hw] with n hn t hnt htn
  exact (hbound n w t hnt htn).trans hn

/-- Convergence-event measurability follows from an integrable stationary
bound on Brownian oscillations, cone scaling and the local volume estimate. -/
theorem convergenceDivisibleEventMeasurable_of_brownian_oscillation_bound
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (hscale : ConeEnvironmentScalingStep 𝒮) (hpos : ConeScaleRadiusStep)
    (X : ℕ → ContinuousPath ℝ → ℝ)
    (hX : Integrable (X 0) (brownianMotion 0))
    (hXpos : ∀ n w, 0 ≤ X n w)
    (hid : ∀ n, IdentDistrib (X n) (X 0) (brownianMotion 0) (brownianMotion 0))
    (hbound : ∀ (n : ℕ) w (t : ℝ≥0), (n : ℝ≥0) ≤ t → t ≤ (n : ℝ≥0) + 1 →
      |w t - w (n : ℝ≥0)| ≤ X n w) :
    ConvergenceDivisibleEventMeasurableStep 𝒮 := by
  apply convergenceDivisibleEventMeasurable_of_brownian_oscillation 𝒮 h27 hscale hpos
  intro a ha
  exact brownian_oscillation_of_identDistrib_bound X hX hXpos hid hbound ha

end MatedCRT
