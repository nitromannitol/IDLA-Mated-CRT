import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.GlobalCompatibility
import MatedCRT.Steps.Sec2.ConeScaleInvariance

/-! # Measurability from global cone harmonic-ball existence -/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls

/-- Almost-sure existence of global cone harmonic-ball families supplies the
fixed-disc local validity needed for stopped-family measurability. The global
existence assumption is separate from the conclusion of Theorem 2.3. -/
theorem coneFamilyAEMeasurableStep_of_global_existence
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt) (h27 : VolumeGrowthStmt)
    (hscale : QuantumConeScalingInput) (hlqg : ConeLQGScalingStep)
    (hglobal : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
      ∀ᵐ ω ∂P, ∃ Λ : ℝ → Set ℂ, IsConeHarmonicBallFamily (μ ω) Λ) :
    ConeFamilyAEMeasurableStep := by
  apply coneFamilyAEMeasurableStep_of_threeQuarterDiskLocalValidity h24 h27 hscale hlqg
  intro γ hγ hγ2 Ω _ P hC hcirc μ hcone b hb
  let : IsProbabilityMeasure P := hcone.1
  have hg := hcone.ae_volumeGrowth_inside_unit hγ hγ2 h27 (R := (3 / 4 : ℝ)) (by norm_num)
  have hs := hlqg γ hγ hγ2 Ω P hC hcirc μ hcone b hb
  have hv := hcone.ae_rescaledVolumeGrowth_inside_unit hγ hγ2 h27 hscale hlqg
    hb (R := (3 / 4 : ℝ)) (by norm_num) (by norm_num)
  filter_upwards [hglobal γ hγ hγ2 Ω P hC hcirc μ hcone, hg, hs, hv] with ω hΛ hg hs hv
  obtain ⟨Λ, hΛ⟩ := hΛ
  exact ⟨threeQuarterDiskLocalValidity_of_global_cone_family hg.1 hg.2 hΛ,
    threeQuarterDiskLocalValidity_of_global_cone_family hs.2.isLocallyFiniteMeasure hv
      (hΛ.rescaledFamily coneHarmonicBallFamilyOnScalingStep hs.1 hb)⟩

end MatedCRT
