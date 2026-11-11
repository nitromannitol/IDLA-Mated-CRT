import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.L1Expectation

/-! # Expected Gaussian multiplicative chaos mass -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- For a jointly measurable centered Gaussian field, the real mass of a
finite-reference GMC approximation is integrable and has the reference
measure as its expectation. -/
theorem gmcApprox_integral_real_apply {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [SFinite P] (σ : Measure E) [IsFiniteMeasure σ]
    (γ : ℝ) (H : Ω → E → ℝ) (S : Set E) (hS : MeasurableSet S)
    (hH : Measurable (fun p : Ω × E => H p.1 p.2))
    (hGaussian : ∀ x, ∃ v : ℝ≥0, HasLaw (fun ω => H ω x) (gaussianReal 0 v) P) :
    Integrable (fun ω => (gmcApprox P σ γ H ω).real S) P ∧
      (∫ ω, (gmcApprox P σ γ H ω).real S ∂P) = σ.real S := by
  have hvar : Measurable (fun x => ∫ ω, (H ω x) ^ 2 ∂P) :=
    (hH.pow_const 2).stronglyMeasurable.integral_prod_left'.measurable
  have hW : Measurable (fun p : Ω × E => ENNReal.ofReal (Real.exp
      (γ * H p.1 p.2 - (γ ^ 2 / 2) * ∫ ω', (H ω' p.2) ^ 2 ∂P))) :=
    (((measurable_const.mul hH).sub
      (measurable_const.mul (hvar.comp measurable_snd))).exp).ennreal_ofReal
  have hm : Measurable (fun ω => (gmcApprox P σ γ H ω) S) := by
    simpa only [gmcApprox, withDensity_apply _ hS] using
      (Measurable.lintegral_prod_right' (ν := σ.restrict S) hW)
  have hmean := gmcApprox_lintegral_apply P σ γ H S hS hH hGaussian
  have hfinite : (∫⁻ ω, (gmcApprox P σ γ H ω) S ∂P) ≠ ∞ := by
    rw [hmean]
    exact measure_ne_top σ S
  constructor
  · exact integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfinite
  · change (∫ ω, ((gmcApprox P σ γ H ω) S).toReal ∂P) = (σ S).toReal
    rw [integral_toReal hm.aemeasurable (ae_lt_top hm hfinite), hmean]

/-- An L¹ limit of normalized chaos masses has the reference expectation. -/
theorem gmcLimit_integral_real_apply {Ω E ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [SFinite P] (σ : Measure E) [IsFiniteMeasure σ]
    (l : Filter ι) [NeBot l] (γ : ℝ) (H : ι → Ω → E → ℝ)
    (μ : Ω → Measure E) (S : Set E) (hS : MeasurableSet S)
    (hH : ∀ᶠ i in l, Measurable (fun p : Ω × E => H i p.1 p.2))
    (hGaussian : ∀ᶠ i in l, ∀ x, ∃ v : ℝ≥0,
      HasLaw (fun ω => H i ω x) (gaussianReal 0 v) P)
    (hμ : Integrable (fun ω => (μ ω).real S) P)
    (hconv : Tendsto (fun i => ∫ ω, |(gmcApprox P σ γ (H i) ω).real S -
      (μ ω).real S| ∂P) l (𝓝 0)) :
    (∫ ω, (μ ω).real S ∂P) = σ.real S := by
  have happrox : ∀ᶠ i in l,
      Integrable (fun ω => (gmcApprox P σ γ (H i) ω).real S) P ∧
      (∫ ω, (gmcApprox P σ γ (H i) ω).real S ∂P) = σ.real S := by
    filter_upwards [hH, hGaussian] with i hi hg
    exact gmcApprox_integral_real_apply P σ γ (H i) S hS hi hg
  exact integral_eq_of_L1_limit P l _ _ _ hμ (happrox.mono fun _ h => h.1)
    (happrox.mono fun _ h => h.2) hconv

end MatedCRT
