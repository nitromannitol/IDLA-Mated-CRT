import MatedCRT.Steps.Sec3.HolderTailNormalization

/-! Hölder discrepancy moments from cutoff excursion tails. -/

open MeasureTheory Set

namespace MatedCRT

/-- A nonnegative Hölder discrepancy with a polynomial excursion tail has
three corresponding mean bounds, according to its Hölder exponent. -/
theorem integral_le_of_holder_probability_tail_cutoff
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Ω → ℝ) {H ℓ T R χ ν C : ℝ}
    (hH : 0 < H) (hℓ : 0 < ℓ) (hℓT : ℓ < T) (hTR : T ≤ R)
    (hχ : 0 < χ) (hν : 0 < ν) (hC : 0 ≤ C) (hD : AEMeasurable D μ)
    (hnonneg : 0 ≤ᵐ[μ] D) (hbound : ∀ᵐ ω ∂μ, D ω ≤ H * R ^ χ)
    (htail : ∀ s ∈ Ioc ℓ T, μ.real {ω | H * s ^ χ < D ω} ≤ C * ℓ ^ ν * s ^ (-ν)) :
    let K := C * (R / T) ^ ν
    (χ < ν → (∫ ω, D ω ∂μ) ≤
      H * (ℓ ^ χ + χ * K * (ℓ ^ χ / (ν - χ)))) ∧
    (χ = ν → (∫ ω, D ω ∂μ) ≤
      H * (ℓ ^ ν + ν * K * (ℓ ^ ν * Real.log (R / ℓ)))) ∧
    (ν < χ → (∫ ω, D ω ∂μ) ≤
      H * (ℓ ^ χ + χ * K * (ℓ ^ ν * R ^ (χ - ν) / (χ - ν)))) := by
  dsimp only
  have hR : 0 ≤ R := (hℓ.trans hℓT).le.trans hTR
  let f : Ω → ℝ := fun ω => (D ω / H) ^ χ⁻¹
  obtain ⟨hfm, hf, hfR, heq, hevents⟩ := holder_tail_normalization μ D hH hχ hR hD hnonneg hbound
  have ht : ∀ s ∈ Ioc ℓ T, μ.real {ω | s < f ω} ≤ C * ℓ ^ ν * s ^ (-ν) := by
    intro s hs
    have he : μ {ω | s < f ω} = μ {ω | H * s ^ χ < D ω} :=
      measure_congr (hevents s (le_of_lt (hℓ.trans hs.1)))
    simpa only [measureReal_def, he] using htail s hs
  have hm := integral_rpow_le_of_probability_tail_cutoff μ f hℓ hℓT hTR hχ hν hC hf hfR hfm ht
  have hi : (∫ ω, D ω ∂μ) = H * ∫ ω, f ω ^ χ ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [heq] with ω hω
    exact hω.symm
  rw [hi]
  exact ⟨fun h => mul_le_mul_of_nonneg_left (hm.1 h) hH.le,
    fun h => mul_le_mul_of_nonneg_left (hm.2.1 h) hH.le,
    fun h => mul_le_mul_of_nonneg_left (hm.2.2 h) hH.le⟩

end MatedCRT

#print axioms MatedCRT.integral_le_of_holder_probability_tail_cutoff
