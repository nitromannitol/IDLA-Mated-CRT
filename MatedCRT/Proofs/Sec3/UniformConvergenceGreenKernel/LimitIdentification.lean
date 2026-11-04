import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.MeasureSupport
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Identification of a continuous Green-kernel limit -/

namespace MatedCRT.GreenEnvironment

open MeasureTheory Set Filter Topology
open scoped ContDiff

/-- Smooth compactly supported tests identify continuous functions on an open
set when the reference measure has full support. -/
theorem eqOn_of_integral_tests {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    [μ.IsOpenPosMeasure] {U : Set ℂ} (hU : IsOpen U) {u v : ℂ → ℝ}
    (hu : ContinuousOn u U) (hv : ContinuousOn v U)
    (h : ∀ f : ℂ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ U →
      ∫ x, f x * (u x - v x) ∂μ = 0) : EqOn u v U := by
  have hloc : LocallyIntegrableOn (u - v) U μ :=
    (hu.sub hv).locallyIntegrableOn hU.measurableSet
  have hae : ∀ᵐ x ∂μ, x ∈ U → (u - v) x = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    intro f hf hfc hfU
    simpa only [smul_eq_mul, Pi.sub_apply] using h f hf hfc hfU
  apply Measure.eqOn_open_of_ae_eq (μ := μ) ?_ hU hu hv
  filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hU.measurableSet] with x hx hxU
  exact sub_eq_zero.mp (hx hxU)

/-- The area-parametrization of the space-filling curve supplies the full
support needed to identify the Green-kernel limit. -/
theorem eqOn_of_integral_tests_of_areaParametrized {μ : Measure ℂ}
    [IsLocallyFiniteMeasure μ] {η : ℝ → ℂ} (hη : IsAreaParametrized μ η)
    {U : Set ℂ} (hU : IsOpen U) {u v : ℂ → ℝ}
    (hu : ContinuousOn u U) (hv : ContinuousOn v U)
    (h : ∀ f : ℂ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ U →
      ∫ x, f x * (u x - v x) ∂μ = 0) : EqOn u v U := by
  let : μ.IsOpenPosMeasure := hη.isOpenPosMeasure
  exact eqOn_of_integral_tests hU hu hv h

end MatedCRT.GreenEnvironment
