import MatedCRT.Steps.Sec3.ProbabilityTailCutoff

/-! Moment estimates from tails known only up to a fixed cutoff. -/

open MeasureTheory Set

namespace MatedCRT

/-- The three moment regimes remain valid when the polynomial tail estimate
is only known through a positive cutoff inside the bounded range. -/
theorem integral_rpow_le_of_probability_tail_cutoff
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) {ℓ T R χ ν C : ℝ}
    (hℓ : 0 < ℓ) (hℓT : ℓ < T) (hTR : T ≤ R) (hχ : 0 < χ)
    (hν : 0 < ν) (hC : 0 ≤ C) (hf : 0 ≤ᵐ[μ] f)
    (hbound : ∀ᵐ ω ∂μ, f ω ≤ R) (hfm : AEMeasurable f μ)
    (htail : ∀ s ∈ Ioc ℓ T, μ.real {ω | s < f ω} ≤ C * ℓ ^ ν * s ^ (-ν)) :
    let K := C * (R / T) ^ ν
    (χ < ν → (∫ ω, f ω ^ χ ∂μ) ≤
      ℓ ^ χ + χ * K * (ℓ ^ χ / (ν - χ))) ∧
    (χ = ν → (∫ ω, f ω ^ χ ∂μ) ≤
      ℓ ^ ν + ν * K * (ℓ ^ ν * Real.log (R / ℓ))) ∧
    (ν < χ → (∫ ω, f ω ^ χ ∂μ) ≤
      ℓ ^ χ + χ * K * (ℓ ^ ν * R ^ (χ - ν) / (χ - ν))) := by
  dsimp only
  have hLR : ℓ ≤ R := hℓT.le.trans hTR
  have hT : 0 < T := hℓ.trans hℓT
  have hR : 0 < R := hT.trans_le hTR
  have hK : 0 ≤ C * (R / T) ^ ν :=
    mul_nonneg hC (Real.rpow_nonneg (div_nonneg hR.le hT.le) _)
  have ht := probability_tail_le_of_cutoff μ f hℓ hℓT hTR hν.le hC htail
  refine ⟨?_, ?_, ?_⟩
  · intro hχν
    exact integral_rpow_le_of_moment_lt_tail μ f hℓ hLR hχ hK hχν hf hbound hfm ht
  · intro heq
    subst χ
    exact integral_rpow_le_of_moment_eq_tail μ f hℓ hLR hν hf hbound hfm ht
  · intro hνχ
    exact integral_rpow_le_of_tail_lt_moment μ f hℓ hLR hχ hK hνχ hf hbound hfm ht

end MatedCRT

#print axioms MatedCRT.integral_rpow_le_of_probability_tail_cutoff
