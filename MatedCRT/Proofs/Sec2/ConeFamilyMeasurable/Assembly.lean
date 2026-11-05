import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.RescaledMeasure

/-! # Assembly of the cone-family measurability step -/

namespace MatedCRT

open MeasureTheory Filter HarmonicBalls

/-- Cone-family measurability follows from strict growth, cone scaling and
volume growth for the original and rescaled measures. -/
theorem coneFamilyAEMeasurableStep_of_rescaledVolumeGrowth
    (h27 : VolumeGrowthStmt) (hgrow : ConeHarmonicBallStrictGrowthStep)
    (hscale : QuantumConeScalingInput) (hlqg : ConeLQGScalingStep)
    (hvgood : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ → ∀ b : ℝ, 0 < b →
      ∀ᵐ ω ∂P, ∃ βminus βplus, VolumeGrowth
        (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) (3 / 4) βminus βplus) :
    ConeFamilyAEMeasurableStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hcone
  let : IsProbabilityMeasure P := hcone.1
  refine ⟨fun T Λ hf => aemeasurable_coneHalfBallPair hγ hγ2 hcone h27 hgrow hf, ?_⟩
  intro b hb T Λ hf
  have hR : ∀ᵐ ω ∂P, 0 < coneScaleRadius γ (hcirc ω) b :=
    (hlqg γ hγ hγ2 Ω P hC hcirc μ hcone b hb).mono fun _ h => h.1
  have hgood : ∀ᵐ ω ∂P,
      IsLocallyFiniteMeasure (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) ∧
      ∃ βminus βplus, VolumeGrowth
        (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) (3 / 4) βminus βplus := by
    filter_upwards [hlqg γ hγ hγ2 Ω P hC hcirc μ hcone b hb,
      hvgood γ hγ hγ2 Ω P hC hcirc μ hcone b hb] with ω hl hv
    exact ⟨hl.2.isLocallyFiniteMeasure, hv⟩
  exact aemeasurable_rescaledHalfBallPair_of_volumeGrowth hγ hγ2 hcone hgrow hb hR
    (hcone.aemeasurable_rescaledMeasure b hR) hgood
    (Sec1.aemeasurable_circleProcess_rescaledCircle hscale hγ hγ2 hcone.2.1 hb) hf

end MatedCRT
