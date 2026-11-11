import Mathlib.Probability.Distributions.Gaussian.Real
import MatedCRT.Defs.GaussianMultiplicativeChaos
import Mathlib.MeasureTheory.Integral.Prod

/-! # Expectation of a variance-normalized Gaussian exponential -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The second moment of a centered Gaussian is its variance parameter. -/
theorem centeredGaussian_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) :
    (∫ ω, (X ω) ^ 2 ∂P) = v := by
  have hmean : (∫ ω, X ω ∂P) = 0 := by
    rw [hX.integral_eq, integral_id_gaussianReal]
  have hv := hX.variance_eq
  rw [variance_eq_integral hX.aemeasurable, hmean] at hv
  simpa using hv

/-- A variance-normalized centered Gaussian exponential has expectation one. -/
theorem centeredGaussian_normalized_exp_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) (γ : ℝ) :
    (∫ ω, Real.exp (γ * X ω - (γ ^ 2 / 2) * ∫ ω', (X ω') ^ 2 ∂P) ∂P) = 1 := by
  rw [centeredGaussian_integral_sq hX]
  simp_rw [Real.exp_sub]
  rw [integral_div]
  have hm : (∫ ω, Real.exp (γ * X ω) ∂P) =
      Real.exp ((v : ℝ) * γ ^ 2 / 2) := by
    simpa [mgf] using mgf_gaussianReal hX γ
  rw [hm]
  have he : (v : ℝ) * γ ^ 2 / 2 = γ ^ 2 / 2 * v := by ring
  rw [he]
  exact div_self (ne_of_gt (Real.exp_pos _))


/-- The variance-normalized exponential is integrable. -/
theorem centeredGaussian_normalized_exp_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) (γ : ℝ) :
    Integrable (fun ω => Real.exp (γ * X ω - (γ ^ 2 / 2) * ∫ ω', (X ω') ^ 2 ∂P)) P := by
  have h := hX.integrable_comp (integrable_exp_mul_gaussianReal (μ := 0) (v := v) γ)
  simpa [Function.comp_def, Real.exp_sub] using
    h.div_const (Real.exp ((γ ^ 2 / 2) * ∫ ω', (X ω') ^ 2 ∂P))

/-- The nonnegative integral of the variance-normalized exponential is one. -/
theorem centeredGaussian_normalized_exp_lintegral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) (γ : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp
      (γ * X ω - (γ ^ 2 / 2) * ∫ ω', (X ω') ^ 2 ∂P)) ∂P) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (centeredGaussian_normalized_exp_integrable hX γ)
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le),
    centeredGaussian_normalized_exp_integral hX γ]
  simp


/-- For a jointly measurable centered Gaussian field, the expected
variance-normalized chaos mass of a measurable set is its reference mass. -/
theorem gmcApprox_lintegral_apply {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [SFinite P] (σ : Measure E) [SFinite σ]
    (γ : ℝ) (H : Ω → E → ℝ) (S : Set E) (hS : MeasurableSet S)
    (hH : Measurable (fun p : Ω × E => H p.1 p.2))
    (hGaussian : ∀ x, ∃ v : ℝ≥0, HasLaw (fun ω => H ω x) (gaussianReal 0 v) P) :
    (∫⁻ ω, (gmcApprox P σ γ H ω) S ∂P) = σ S := by
  have hvar : Measurable (fun x => ∫ ω, (H ω x) ^ 2 ∂P) :=
    (hH.pow_const 2).stronglyMeasurable.integral_prod_left'.measurable
  have hW : Measurable (fun p : Ω × E => ENNReal.ofReal (Real.exp
      (γ * H p.1 p.2 - (γ ^ 2 / 2) * ∫ ω', (H ω' p.2) ^ 2 ∂P))) := by
    exact (((measurable_const.mul hH).sub
      (measurable_const.mul (hvar.comp measurable_snd))).exp).ennreal_ofReal
  simp only [gmcApprox, withDensity_apply _ hS]
  rw [lintegral_lintegral_swap hW.aemeasurable]
  have hpoint : ∀ x, (∫⁻ ω, ENNReal.ofReal (Real.exp
      (γ * H ω x - (γ ^ 2 / 2) * ∫ ω', (H ω' x) ^ 2 ∂P)) ∂P) = 1 := by
    intro x
    obtain ⟨v, hv⟩ := hGaussian x
    exact centeredGaussian_normalized_exp_lintegral hv γ
  simp_rw [hpoint]
  simp

end MatedCRT
