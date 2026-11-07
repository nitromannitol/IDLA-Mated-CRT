import MatedCRT.Defs.GaussianMultiplicativeChaos
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def

/-!
# Log-correlated Gaussian generalized fields

The admissible measures and field covariance follow Berestycki,
*An elementary approach to Gaussian multiplicative chaos*,
arXiv:1506.09113v2, equation (1.2), p. 2.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The real-valued representative of a log-correlated covariance kernel.
Its arbitrary diagonal value is harmless for finite-energy measures. -/
noncomputable def logCovarianceKernel {E : Type*} [PseudoMetricSpace E]
    (g : E → E → ℝ) (x y : E) : ℝ := Real.log (dist x y)⁻¹ + g x y

/-- The absolute covariance kernel, with its logarithmic singularity set to
`∞` on the diagonal. -/
noncomputable def absLogCovarianceKernel {E : Type*} [PseudoMetricSpace E]
    (g : E → E → ℝ) (x y : E) : ℝ≥0∞ :=
  if dist x y = 0 then ⊤ else ENNReal.ofReal |logCovarianceKernel g x y|

/-- The signed finite-energy measures in a domain, denoted `M` by
Berestycki. Finite energy is taken with respect to the total variation. -/
def IsLogFieldObservable {E : Type*} [MetricSpace E] [MeasurableSpace E]
    (D : Set E) (g : E → E → ℝ) (ρ : SignedMeasure E) : Prop :=
  ρ.totalVariation Dᶜ = 0 ∧
    (∫⁻ x, ∫⁻ y, absLogCovarianceKernel g x y ∂ρ.totalVariation
      ∂ρ.totalVariation) < ⊤

/-- The integrated covariance of two finite-energy signed measures. -/
noncomputable def logFieldCovariance {E : Type*} [MetricSpace E] [MeasurableSpace E]
    (g : E → E → ℝ) (ρ ν : SignedMeasure E) : ℝ :=
  ∫ᵛ x, ∫ᵛ y, logCovarianceKernel g x y ∂•ν ∂•ρ

/-- A centered log-correlated Gaussian generalized field, indexed by the
signed finite-energy measures in `D`. Linearity is understood almost surely
for each fixed pair of observables, as in Berestycki's definition. -/
structure IsLogCorrelatedField {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
    [MeasurableSpace E] (P : Measure Ω) (D : Set E) (g : E → E → ℝ)
    (h : SignedMeasure E → Ω → ℝ) : Prop where
  /-- The indexed family is jointly Gaussian. -/
  gaussian : IsGaussianProcess (fun ρ : {ρ // IsLogFieldObservable D g ρ} => h ρ.1) P
  /-- Each observable is centered. -/
  centered : ∀ ρ, IsLogFieldObservable D g ρ → ∫ ω, h ρ ω ∂P = 0
  /-- The covariance is the integrated log-correlated kernel. -/
  covariance : ∀ ρ ν, IsLogFieldObservable D g ρ → IsLogFieldObservable D g ν →
    cov[h ρ, h ν; P] = logFieldCovariance g ρ ν
  /-- Additivity for each fixed pair for which all terms are admissible. -/
  additive : ∀ ρ ν, IsLogFieldObservable D g ρ → IsLogFieldObservable D g ν →
    IsLogFieldObservable D g (ρ + ν) →
    ∀ᵐ ω ∂P, h (ρ + ν) ω = h ρ ω + h ν ω
  /-- Homogeneity for each fixed scalar and observable. -/
  homogeneous : ∀ (a : ℝ) ρ, IsLogFieldObservable D g ρ →
    IsLogFieldObservable D g (a • ρ) →
    ∀ᵐ ω ∂P, h (a • ρ) ω = a * h ρ ω

end MatedCRT
