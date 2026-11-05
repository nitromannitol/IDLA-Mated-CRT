import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.ScaledUniqueness
import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.MeasureLaw

/-! # Transfer of half-ball horizon uniqueness under the measure law -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Set HarmonicBalls

/-- Measures for which every pair of stopped harmonic-ball families has the
same half-ball horizon. -/
def halfBallHorizonUniqueMeasures : Set (Measure ℂ) :=
  {ν | ∀ (T S : ℝ) (Λ Γ : ℝ → Set ℂ),
    0 < T → IsConeHarmonicBallFamilyOn ν Λ T → IsStoppedAtHalfBall Λ T →
    0 < S → IsConeHarmonicBallFamilyOn ν Γ S → IsStoppedAtHalfBall Γ S → S = T}

/-- Measure-law null measurability of the stopped-horizon uniqueness event.
This is an intermediate descriptive-set-theoretic assertion, not an external
literature input. -/
def ConeHorizonUniqueLawMeasurabilityStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
    NullMeasurableSet halfBallHorizonUniqueMeasures (P.map μ)

/-- The uniqueness event transfers to the rescaled measure whenever it is
null measurable under the original measure law. -/
theorem coneRescaledHalfBallHorizonUniqueStep_of_lawMeasurability
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (hnull : ConeHorizonUniqueLawMeasurabilityStep)
    (hscale : QuantumConeScalingInput) (hlqg : ConeLQGScalingStep) :
    ConeRescaledHalfBallHorizonUniqueStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hcone b hb
  let : IsProbabilityMeasure P := hcone.1
  have hU : ∀ᵐ ω ∂P, μ ω ∈ halfBallHorizonUniqueMeasures := by
    filter_upwards [h24 γ hγ hγ2 Ω P hC hcirc μ hcone] with ω hω
    obtain ⟨T₀, hT₀, Λ₀, hΛ₀, hs₀, hu⟩ := hω
    intro T S Λ Γ hT hΛ hsΛ hS hΓ hsΓ
    exact ((hu S Γ hS hΓ hsΓ).1).trans ((hu T Λ hT hΛ hsΛ).1).symm
  obtain ⟨E, hEU, hEm, hEeq⟩ :=
    (hnull γ hγ hγ2 Ω P hC hcirc μ hcone).exists_measurable_subset_ae_eq
  have heq : ∀ᵐ ω ∂P, (μ ω ∈ E) ↔ (μ ω ∈ halfBallHorizonUniqueMeasures) := by
    filter_upwards [ae_of_ae_map hcone.aemeasurable_lqgMeasure hEeq] with ω hω
    exact propext_iff.mp hω
  have hE : ∀ᵐ ω ∂P, μ ω ∈ E := by
    filter_upwards [hU, heq] with ω hω he
    exact he.mpr hω
  have hid := hcone.identDistrib_rescaledMeasure hγ hγ2 hscale hlqg hb
  have hE' := hid.symm.ae_mem_snd hEm hE
  have hR := (hlqg γ hγ hγ2 Ω P hC hcirc μ hcone b hb).mono fun _ h => h.1
  filter_upwards [hE', hR] with ω hω hRω
  intro T S Λ Γ hT hΛ hsΛ hS hΓ hsΓ
  apply hEU hω T S (rescaledFamily Λ (coneScaleRadius γ (hcirc ω) b) b)
    (rescaledFamily Γ (coneScaleRadius γ (hcirc ω) b) b) hT
    (coneHarmonicBallFamilyOnScalingStep (μ ω) Λ _ b T hRω hb hΛ) hsΛ hS
    (coneHarmonicBallFamilyOnScalingStep (μ ω) Γ _ b S hRω hb hΓ) hsΓ

/-- The cone-family measurability step follows from Lemma 2.4 and the
null-measurability of the horizon uniqueness event. -/
theorem coneFamilyAEMeasurableStep_of_horizonLawMeasurability
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (hnull : ConeHorizonUniqueLawMeasurabilityStep)
    (h27 : VolumeGrowthStmt) (hscale : QuantumConeScalingInput)
    (hlqg : ConeLQGScalingStep) : ConeFamilyAEMeasurableStep :=
  coneFamilyAEMeasurableStep_of_rescaledHorizonUnique h24
    (coneRescaledHalfBallHorizonUniqueStep_of_lawMeasurability h24 hnull hscale hlqg)
    h27 hscale hlqg

end MatedCRT
