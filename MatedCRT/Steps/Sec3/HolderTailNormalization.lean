import MatedCRT.Steps.Sec3.BoundedMomentCutoff

/-! Normalize a nonnegative Hölder discrepancy to an excursion scale. -/

open MeasureTheory Set

namespace MatedCRT

/-- Taking the inverse Hölder power converts a bounded nonnegative
function into a bounded distance variable with the corresponding tails. -/
theorem holder_tail_normalization {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (D : Ω → ℝ) {H χ R : ℝ}
    (hH : 0 < H) (hχ : 0 < χ) (hR : 0 ≤ R)
    (hD : AEMeasurable D μ) (hnonneg : 0 ≤ᵐ[μ] D)
    (hbound : ∀ᵐ ω ∂μ, D ω ≤ H * R ^ χ) :
    let f : Ω → ℝ := fun ω => (D ω / H) ^ χ⁻¹
    AEMeasurable f μ ∧ (0 ≤ᵐ[μ] f) ∧ (∀ᵐ ω ∂μ, f ω ≤ R) ∧
      (∀ᵐ ω ∂μ, H * f ω ^ χ = D ω) ∧
      (∀ s : ℝ, 0 ≤ s → {ω | s < f ω} =ᵐ[μ] {ω | H * s ^ χ < D ω}) := by
  dsimp only
  have hmeas : AEMeasurable (fun ω => (D ω / H) ^ χ⁻¹) μ :=
    (Real.continuous_rpow_const (inv_nonneg.mpr hχ.le)).measurable.comp_aemeasurable
      (hD.div_const H)
  refine ⟨hmeas, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hnonneg] with ω hω
    exact Real.rpow_nonneg (div_nonneg hω hH.le) _
  · filter_upwards [hnonneg, hbound] with ω hω hb
    have hdiv : D ω / H ≤ R ^ χ := (div_le_iff₀ hH).2 (by simpa [mul_comm] using hb)
    have ht := Real.rpow_le_rpow (div_nonneg hω hH.le) hdiv (inv_nonneg.mpr hχ.le)
    simpa [Real.rpow_rpow_inv hR hχ.ne'] using ht
  · filter_upwards [hnonneg] with ω hω
    rw [Real.rpow_inv_rpow (div_nonneg hω hH.le) hχ.ne']
    field_simp
  · intro s hs
    filter_upwards [hnonneg] with ω hω
    apply propext
    have hroot : 0 ≤ (D ω / H) ^ χ⁻¹ := Real.rpow_nonneg (div_nonneg hω hH.le) _
    rw [← Real.rpow_lt_rpow_iff hs hroot hχ,
      Real.rpow_inv_rpow (div_nonneg hω hH.le) hχ.ne']
    simpa [mul_comm] using (lt_div_iff₀ hH)

end MatedCRT

#print axioms MatedCRT.holder_tail_normalization
