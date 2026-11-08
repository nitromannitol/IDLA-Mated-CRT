import MatedCRT.Steps.Sec3.BoundedMomentTail
import MatedCRT.Steps.Sec3.ProbabilityTailRates

/-! Moment estimates from polynomial probability tails. -/

open MeasureTheory Set

namespace MatedCRT

/-- A moment below the tail exponent is controlled by the lower cutoff. -/
theorem integral_rpow_le_of_moment_lt_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    {ℓ R χ ν C : ℝ} (hℓ : 0 < ℓ) (hLR : ℓ ≤ R) (hχ : 0 < χ)
    (hC : 0 ≤ C) (hχν : χ < ν) (hf : 0 ≤ᵐ[μ] f)
    (hbound : ∀ᵐ ω ∂μ, f ω ≤ R) (hfm : AEMeasurable f μ)
    (htail : ∀ s ∈ Ioo ℓ R, μ.real {ω | s < f ω} ≤ C * ℓ ^ ν * s ^ (-ν)) :
    (∫ ω, f ω ^ χ ∂μ) ≤ ℓ ^ χ + χ * C * (ℓ ^ χ / (ν - χ)) := by
  rw [integral_rpow_eq_integral_probability_tail μ f hχ (le_trans hℓ.le hLR) hf hbound hfm]
  exact integral_probability_tail_le_of_moment_lt_tail μ f hℓ hLR hχ hC hχν htail

/-- At the tail exponent, the moment estimate has a logarithmic factor. -/
theorem integral_rpow_le_of_moment_eq_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    {ℓ R ν C : ℝ} (hℓ : 0 < ℓ) (hLR : ℓ ≤ R) (hν : 0 < ν)
    (hf : 0 ≤ᵐ[μ] f) (hbound : ∀ᵐ ω ∂μ, f ω ≤ R) (hfm : AEMeasurable f μ)
    (htail : ∀ s ∈ Ioo ℓ R, μ.real {ω | s < f ω} ≤ C * ℓ ^ ν * s ^ (-ν)) :
    (∫ ω, f ω ^ ν ∂μ) ≤ ℓ ^ ν + ν * C * (ℓ ^ ν * Real.log (R / ℓ)) := by
  rw [integral_rpow_eq_integral_probability_tail μ f hν (le_trans hℓ.le hLR) hf hbound hfm]
  exact integral_probability_tail_le_of_moment_eq_tail μ f hℓ hLR hν htail

/-- A moment above the tail exponent is controlled by the upper cutoff. -/
theorem integral_rpow_le_of_tail_lt_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    {ℓ R χ ν C : ℝ} (hℓ : 0 < ℓ) (hLR : ℓ ≤ R) (hχ : 0 < χ)
    (hC : 0 ≤ C) (hνχ : ν < χ) (hf : 0 ≤ᵐ[μ] f)
    (hbound : ∀ᵐ ω ∂μ, f ω ≤ R) (hfm : AEMeasurable f μ)
    (htail : ∀ s ∈ Ioo ℓ R, μ.real {ω | s < f ω} ≤ C * ℓ ^ ν * s ^ (-ν)) :
    (∫ ω, f ω ^ χ ∂μ) ≤ ℓ ^ χ + χ * C * (ℓ ^ ν * R ^ (χ - ν) / (χ - ν)) := by
  rw [integral_rpow_eq_integral_probability_tail μ f hχ (le_trans hℓ.le hLR) hf hbound hfm]
  exact integral_probability_tail_le_of_tail_lt_moment μ f hℓ hLR hχ hC hνχ htail

end MatedCRT

#print axioms MatedCRT.integral_rpow_le_of_moment_lt_tail
#print axioms MatedCRT.integral_rpow_le_of_moment_eq_tail
#print axioms MatedCRT.integral_rpow_le_of_tail_lt_moment
