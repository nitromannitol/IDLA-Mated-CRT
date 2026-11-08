import MatedCRT.Steps.Sec3.ProbabilityTailIntegrable

/-! Three regimes for integrated probability tails. -/

open MeasureTheory Set

namespace MatedCRT

/-- Below the tail exponent, the lower cutoff controls the integrated moment tail. -/
theorem integral_probability_tail_le_of_moment_lt_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) {ℓ R χ ν C : ℝ} (hℓ : 0 < ℓ) (hLR : ℓ ≤ R)
    (hχ : 0 < χ) (hC : 0 ≤ C) (hχν : χ < ν)
    (htail : ∀ s ∈ Ioo ℓ R, μ.real {ω | s < f ω} ≤ C * ℓ ^ ν * s ^ (-ν)) :
    χ * (∫ s in 0..R, s ^ (χ - 1) * μ.real {ω | s < f ω}) ≤
      ℓ ^ χ + χ * C * (ℓ ^ χ / (ν - χ)) := by
  exact (integral_probability_tail_le μ f hℓ hLR hχ htail).trans
    (add_le_add_right (mul_le_mul_of_nonneg_left
      (power_tail_integral_le_of_moment_lt_tail hℓ hLR hχν) (mul_nonneg hχ.le hC)) _)

/-- At the tail exponent, the integrated moment tail has a logarithmic factor. -/
theorem integral_probability_tail_le_of_moment_eq_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) {ℓ R ν C : ℝ} (hℓ : 0 < ℓ) (hLR : ℓ ≤ R)
    (hν : 0 < ν)
    (htail : ∀ s ∈ Ioo ℓ R, μ.real {ω | s < f ω} ≤ C * ℓ ^ ν * s ^ (-ν)) :
    ν * (∫ s in 0..R, s ^ (ν - 1) * μ.real {ω | s < f ω}) ≤
      ℓ ^ ν + ν * C * (ℓ ^ ν * Real.log (R / ℓ)) := by
  simpa only [integral_power_tail_critical hℓ hLR] using
    (integral_probability_tail_le μ f hℓ hLR hν htail)

/-- Above the tail exponent, the upper cutoff controls the integrated moment tail. -/
theorem integral_probability_tail_le_of_tail_lt_moment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) {ℓ R χ ν C : ℝ} (hℓ : 0 < ℓ) (hLR : ℓ ≤ R)
    (hχ : 0 < χ) (hC : 0 ≤ C) (hνχ : ν < χ)
    (htail : ∀ s ∈ Ioo ℓ R, μ.real {ω | s < f ω} ≤ C * ℓ ^ ν * s ^ (-ν)) :
    χ * (∫ s in 0..R, s ^ (χ - 1) * μ.real {ω | s < f ω}) ≤
      ℓ ^ χ + χ * C * (ℓ ^ ν * R ^ (χ - ν) / (χ - ν)) := by
  exact (integral_probability_tail_le μ f hℓ hLR hχ htail).trans
    (add_le_add_right (mul_le_mul_of_nonneg_left
      (power_tail_integral_le_of_tail_lt_moment hℓ hLR hνχ) (mul_nonneg hχ.le hC)) _)

end MatedCRT

#print axioms MatedCRT.integral_probability_tail_le_of_moment_lt_tail
#print axioms MatedCRT.integral_probability_tail_le_of_moment_eq_tail
#print axioms MatedCRT.integral_probability_tail_le_of_tail_lt_moment
