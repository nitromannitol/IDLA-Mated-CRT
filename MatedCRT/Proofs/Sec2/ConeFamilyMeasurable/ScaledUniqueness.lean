import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.RadialContainment
import MatedCRT.Proofs.Sec2.ConeFamily

/-! # Uniqueness of the rescaled half-ball horizon -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls TopologicalSpace
open scoped ENNReal

/-- The uniqueness part of the rescaled half-ball construction. This is an
intermediate step: it asserts neither existence nor equality in law. -/
def ConeRescaledHalfBallHorizonUniqueStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∀ b : ℝ, 0 < b → ∀ᵐ ω ∂P,
    ∀ (T S : ℝ) (Λ Γ : ℝ → Set ℂ),
      0 < T → IsConeHarmonicBallFamilyOn (μ ω) Λ (b * T) →
      IsStoppedAtHalfBall (rescaledFamily Λ (coneScaleRadius γ (hcirc ω) b) b) T →
      0 < S → IsConeHarmonicBallFamilyOn (μ ω) Γ (b * S) →
      IsStoppedAtHalfBall (rescaledFamily Γ (coneScaleRadius γ (hcirc ω) b) b) S → S = T

/-- Strict growth and positivity of the cone scaling radius imply uniqueness
of the rescaled half-ball horizon. -/
theorem coneRescaledHalfBallHorizonUniqueStep_of_strictGrowth
    (hgrow : ConeHarmonicBallStrictGrowthStep) (hscale : QuantumConeScalingInput) :
    ConeRescaledHalfBallHorizonUniqueStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hcone b hb
  have hpos := coneScaleRadiusPosStep_of_input hscale γ hγ hγ2 Ω P hC hcirc hcone.1 hcone.2.1 b hb
  filter_upwards [hgrow γ hγ hγ2 Ω P hC hcirc μ hcone, hpos] with ω hg hR
  intro T S Λ Γ hT hΛ hsΛ hS hΓ hsΓ
  have hΛ' := coneHarmonicBallFamilyOnScalingStep (μ ω) Λ _ b T hR hb hΛ
  have hΓ' := coneHarmonicBallFamilyOnScalingStep (μ ω) Γ _ b S hR hb hΓ
  exact (hsΛ.eq_of_eqOn hsΓ (hΛ'.eqOn hΓ') hΛ'.2.1.monotoneOn hΓ'.2.1.monotoneOn
    ((hg (b * T) Λ hΛ).rescaledFamily hb) ((hg (b * S) Γ hΓ).rescaledFamily hb)).symm

/-- Lemmas 2.4 and 2.5 imply the rescaled horizon uniqueness step. -/
theorem coneRescaledHalfBallHorizonUniqueStep_of_lemmas
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt) (h25 : ConeScaleInvarianceUpToFixedTimeStmt) :
    ConeRescaledHalfBallHorizonUniqueStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hcone b hb
  have hex : ∀ᵐ ω ∂P, ∃ y : ℝ × (ℝ → Set ℂ),
      0 < y.1 ∧ IsConeHarmonicBallFamilyOn (μ ω) y.2 y.1 ∧ IsStoppedAtHalfBall y.2 y.1 := by
    filter_upwards [h24 γ hγ hγ2 Ω P hC hcirc μ hcone] with ω hω
    obtain ⟨T, hT, Λ, hΛ, hs, _⟩ := hω
    exact ⟨(T, Λ), hT, hΛ, hs⟩
  let x : Ω → ℝ × (ℝ → Set ℂ) := fun ω => Classical.epsilon fun y =>
    0 < y.1 ∧ IsConeHarmonicBallFamilyOn (μ ω) y.2 y.1 ∧ IsStoppedAtHalfBall y.2 y.1
  have hx : ∀ᵐ ω ∂P, 0 < (x ω).1 ∧ IsConeHarmonicBallFamilyOn (μ ω) (x ω).2 (x ω).1 ∧
      IsStoppedAtHalfBall (x ω).2 (x ω).1 := by
    filter_upwards [hex] with ω hω
    exact Classical.epsilon_spec hω
  obtain ⟨T₀, Λ₀, hbase, _⟩ :=
    h25 γ hγ hγ2 Ω P hC hcirc μ hcone (fun ω => (x ω).1) (fun ω => (x ω).2) hx b hb
  filter_upwards [hbase] with ω hω
  intro T S Λ Γ hT hΛ hsΛ hS hΓ hsΓ
  exact ((hω.2.2.2 S Γ hS hΓ hsΓ).1).trans ((hω.2.2.2 T Λ hT hΛ hsΛ).1).symm

/-- Measurability needs only rescaled horizon uniqueness, rather than the
joint-law assertion of Lemma 2.5. -/
theorem coneFamilyAEMeasurableStep_of_rescaledHorizonUnique
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (huniq : ConeRescaledHalfBallHorizonUniqueStep)
    (h27 : VolumeGrowthStmt) (hscale : QuantumConeScalingInput)
    (hlqg : ConeLQGScalingStep) : ConeFamilyAEMeasurableStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hcone
  let : IsProbabilityMeasure P := hcone.1
  have h24ae := h24 γ hγ hγ2 Ω P hC hcirc μ hcone
  constructor
  · intro T Λ hf
    apply hcone.2.1.measurable_circleProcess.aemeasurable.prodMk
    apply aemeasurable_halfBallFamily_of_radial_containment hcone.aemeasurable_lqgMeasure
      (hcone.ae_volumeGrowth_inside_unit hγ hγ2 h27 (by norm_num))
    filter_upwards [hf, h24ae] with ω hω hgood
    refine ⟨hω.1, hω.2.1, hω.2.2, ?_⟩
    obtain ⟨T₀, hT₀, Λ₀, hΛ₀, hs₀, huniq⟩ := hgood
    have heq := (huniq (T ω) (Λ ω) hω.1 hω.2.1 hω.2.2).1
    apply radial_containment_of_unique_stopped_family hω.2.1 hω.2.2
    intro S Γ hS hΓ hsΓ
    exact ((huniq S Γ hS hΓ hsΓ).1).trans heq.symm
  · intro b hb T Λ hf
    have hbase := huniq γ hγ hγ2 Ω P hC hcirc μ hcone b hb
    have hs := hlqg γ hγ hγ2 Ω P hC hcirc μ hcone b hb
    have hR : ∀ᵐ ω ∂P, 0 < coneScaleRadius γ (hcirc ω) b := hs.mono fun _ h => h.1
    have hgood : ∀ᵐ ω ∂P,
        IsLocallyFiniteMeasure (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) ∧
        ∃ βm βp, VolumeGrowth (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b)
          (3 / 4) βm βp := by
      filter_upwards [hs, hcone.ae_rescaledVolumeGrowth_inside_unit hγ hγ2 h27 hscale hlqg
        hb (R := (3 / 4 : ℝ)) (by norm_num) (by norm_num)] with ω hω hv
      exact ⟨hω.2.isLocallyFiniteMeasure, hv⟩
    apply (Sec1.aemeasurable_circleProcess_rescaledCircle hscale hγ hγ2 hcone.2.1 hb).prodMk
    apply aemeasurable_halfBallFamily_of_radial_containment
      (hcone.aemeasurable_rescaledMeasure b hR) hgood
    filter_upwards [hf, hbase, hR] with ω hω hbaseω hRω
    refine ⟨hω.1, coneHarmonicBallFamilyOnScalingStep (μ ω) (Λ ω) _ b (T ω)
      hRω hb hω.2.1, hω.2.2, ?_⟩
    intro t ht
    by_contra h
    push Not at h
    obtain ⟨S, htS, hST⟩ := exists_between ht.2
    have hS : 0 < S := ht.1.trans htS
    have hsS := hω.2.2.restrict_of_early_contact hST.le ⟨ht.1, htS⟩ h
    have hfS : IsConeHarmonicBallFamilyOn (μ ω) (Λ ω) (b * S) :=
      hω.2.1.restrict_time (mul_pos hb hS) (mul_le_mul_of_nonneg_left hST.le hb.le)
    have heq := hbaseω (T ω) S (Λ ω) (Λ ω) hω.1 hω.2.1 hω.2.2 hS hfS hsS
    exact (ne_of_lt hST) heq

end MatedCRT
