import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.ContactEvent

/-! # Transfer of horizon uniqueness through the fixed-disc contact event -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Set Metric HarmonicBalls TopologicalSpace

/-- The regularized clusters in the three-quarter disk form a local cone
harmonic-ball family through every rational time at which the cluster is
contained in the closed half disk. -/
def ThreeQuarterDiskLocalValidity (ν : Measure ℂ) : Prop :=
  ∀ r : PositiveRational,
    (∀ n : ℕ, denseSeq ℂ n ∈ interior (closure (cluster ν (3 / 4) 0 r)) →
      denseSeq ℂ n ∈ closedBall (0 : ℂ) (1 / 2)) →
    ∃ Λ : ℝ → Set ℂ, IsConeHarmonicBallFamilyOn ν Λ r ∧
      ∀ t (_ht : t ∈ Ioo 0 (r : ℝ)),
        interior (closure (cluster ν (3 / 4) 0 t)) = Λ t

/-- Horizon uniqueness transfers between identically distributed measures
when the fixed-disc clusters satisfy local validity on both sides. -/
theorem IdentDistrib.ae_halfBallHorizonUnique_of_local_validity
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {μ ν : Ω → Measure ℂ} (hdis : IdentDistrib μ ν P P)
    (hμ : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧
      (∃ βm βp, VolumeGrowth (μ ω) (3 / 4) βm βp) ∧
      ThreeQuarterDiskLocalValidity (μ ω) ∧ μ ω ∈ halfBallHorizonUniqueMeasures)
    (hν : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (ν ω) ∧
      (∃ βm βp, VolumeGrowth (ν ω) (3 / 4) βm βp) ∧
      ThreeQuarterDiskLocalValidity (ν ω)) :
    ∀ᵐ ω ∂P, ν ω ∈ halfBallHorizonUniqueMeasures := by
  obtain ⟨E, hE, htest⟩ := exists_measurable_halfBallHorizonNonunique_of_local_validity
  have hμE : ∀ᵐ ω ∂P, μ ω ∈ Eᶜ := by
    filter_upwards [hμ] with ω hω
    exact fun h => (htest (μ ω) hω.1 hω.2.1 hω.2.2.1).mp h hω.2.2.2
  have hνE : ∀ᵐ ω ∂P, ν ω ∈ Eᶜ := hdis.ae_mem_snd hE.compl hμE
  filter_upwards [hν, hνE] with ω hω hn
  by_contra hnot
  exact hn ((htest (ν ω) hω.1 hω.2.1 hω.2.2).mpr hnot)

/-- Local validity for the cone measure and its rescalings, together with
Lemma 2.4 and the volume-growth and scaling inputs, gives the assigned
cone-family measurability step. -/
theorem coneFamilyAEMeasurableStep_of_threeQuarterDiskLocalValidity
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt) (h27 : VolumeGrowthStmt)
    (hscale : QuantumConeScalingInput) (hlqg : ConeLQGScalingStep)
    (hlocal : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ → ∀ b : ℝ, 0 < b →
      ∀ᵐ ω ∂P, ThreeQuarterDiskLocalValidity (μ ω) ∧
        ThreeQuarterDiskLocalValidity
          (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b)) :
    ConeFamilyAEMeasurableStep := by
  apply coneFamilyAEMeasurableStep_of_rescaledHorizonUnique h24 ?_ h27 hscale hlqg
  intro γ hγ hγ2 Ω _ P hC hcirc μ hcone b hb
  let : IsProbabilityMeasure P := hcone.1
  have hgood := hcone.ae_volumeGrowth_inside_unit hγ hγ2 h27 (R := (3 / 4 : ℝ)) (by norm_num)
  have hs := hlqg γ hγ hγ2 Ω P hC hcirc μ hcone b hb
  have hscaled := hcone.ae_rescaledVolumeGrowth_inside_unit hγ hγ2 h27 hscale hlqg
    hb (R := (3 / 4 : ℝ)) (by norm_num) (by norm_num)
  have hvalid := hlocal γ hγ hγ2 Ω P hC hcirc μ hcone b hb
  have hu : ∀ᵐ ω ∂P, μ ω ∈ halfBallHorizonUniqueMeasures := by
    filter_upwards [h24 γ hγ hγ2 Ω P hC hcirc μ hcone] with ω hω
    obtain ⟨T₀, hT₀, Λ₀, hΛ₀, hs₀, hunique⟩ := hω
    intro T S Λ Γ hT hΛ hsΛ hS hΓ hsΓ
    exact ((hunique S Γ hS hΓ hsΓ).1).trans ((hunique T Λ hT hΛ hsΛ).1).symm
  have horig : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧
      (∃ βm βp, VolumeGrowth (μ ω) (3 / 4) βm βp) ∧
      ThreeQuarterDiskLocalValidity (μ ω) ∧ μ ω ∈ halfBallHorizonUniqueMeasures := by
    filter_upwards [hgood, hvalid, hu] with ω hg hv huω
    exact ⟨hg.1, hg.2, hv.1, huω⟩
  have hrescale : ∀ᵐ ω ∂P,
      IsLocallyFiniteMeasure (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) ∧
      (∃ βm βp, VolumeGrowth
        (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) (3 / 4) βm βp) ∧
      ThreeQuarterDiskLocalValidity
        (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) := by
    filter_upwards [hs, hscaled, hvalid] with ω hl hv hlocalω
    exact ⟨hl.2.isLocallyFiniteMeasure, hv, hlocalω.2⟩
  have hU := IdentDistrib.ae_halfBallHorizonUnique_of_local_validity
    (hcone.identDistrib_rescaledMeasure hγ hγ2 hscale hlqg hb).symm horig hrescale
  filter_upwards [hU, hs] with ω hω hR
  intro T S Λ Γ hT hΛ hsΛ hS hΓ hsΓ
  exact hω T S (rescaledFamily Λ (coneScaleRadius γ (hcirc ω) b) b)
    (rescaledFamily Γ (coneScaleRadius γ (hcirc ω) b) b) hT
    (coneHarmonicBallFamilyOnScalingStep (μ ω) Λ _ b T hR.1 hb hΛ) hsΛ hS
    (coneHarmonicBallFamilyOnScalingStep (μ ω) Γ _ b S hR.1 hb hΓ) hsΓ

end MatedCRT
