import MatedCRT.FirstPass.Derived.ConeRadiusTails

/-!
# Uniform bounds for cone scale radii

Last-visit radii increase with the positive mass parameter. For a quantum cone,
the upper tail at one fixed parameter controls the union of the upper-tail
events over all smaller positive parameters.
-/

open Filter MeasureTheory Set HarmonicBalls
open scoped ENNReal

namespace MatedCRT.FirstPass.Derived

/-- The last-visit radius is monotone in the positive level parameter. -/
theorem coneScaleRadius_le_of_le {γ : ℝ} {hcirc : ℝ → ℂ → ℝ} {a b : ℝ}
    (hγ : 0 < γ) (ha : 0 < a) (hab : a ≤ b)
    (hcont : Continuous fun s : ℝ => hcirc (Real.exp s) 0)
    (hup : Tendsto (fun s : ℝ => hcirc (Real.exp s) 0 + lqgQ γ * s) atTop atTop)
    (hdown : Tendsto (fun s : ℝ => hcirc (Real.exp s) 0 + lqgQ γ * s) atBot atBot) :
    coneScaleRadius γ hcirc a ≤ coneScaleRadius γ hcirc b := by
  have ha_spec := coneScaleRadius_spec (b := a) hcont hup hdown
  have hb_spec := coneScaleRadius_spec (b := b) hcont hup hdown
  have hlevel : γ⁻¹ * Real.log a ≤ γ⁻¹ * Real.log b :=
    mul_le_mul_of_nonneg_left (Real.log_le_log ha hab) (inv_nonneg.mpr hγ.le)
  by_contra hnot
  have hstrict := hb_spec.2.2 _ (lt_of_not_ge hnot)
  rw [ha_spec.2.1] at hstrict
  exact (not_lt_of_ge hlevel) hstrict

/-- A quantum cone has monotone scale radii for all positive parameters on one event. -/
theorem ae_coneScaleRadius_mono {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (h : IsQuantumCone γ P hC hcirc) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ, 0 < a → a ≤ b →
      coneScaleRadius γ (hcirc ω) a ≤ coneScaleRadius γ (hcirc ω) b := by
  filter_upwards [ae_coneRadialLevel hγ hγ2 h] with ω hω
  intro a b ha hab
  exact coneScaleRadius_le_of_le hγ ha hab hω.1 hω.2.1 hω.2.2

/-- The upper tail is uniform over all positive parameters up to a fixed bound. -/
theorem exists_measure_coneScaleRadius_sup_le {Ω : Type} [MeasurableSpace Ω] {γ : ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (h : IsQuantumCone γ P hC hcirc) {B : ℝ}
    {θ : ℝ≥0∞} (hθ : 0 < θ) :
    ∃ M : ℝ, P {ω | ∃ b : ℝ, 0 < b ∧ b ≤ B ∧ M < coneScaleRadius γ (hcirc ω) b} ≤ θ := by
  obtain ⟨M, hM⟩ := exists_measure_gt_le_coneScaleRadius hγ hγ2 h B hθ
  refine ⟨M, (measure_mono_ae ?_).trans hM⟩
  filter_upwards [ae_coneScaleRadius_mono hγ hγ2 h] with ω hmono
  rintro ⟨b, hb, hbB, hMb⟩
  exact lt_of_lt_of_le hMb (hmono b B hb hbB)

end MatedCRT.FirstPass.Derived
