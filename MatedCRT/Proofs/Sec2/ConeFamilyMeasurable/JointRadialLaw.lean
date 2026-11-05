import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.ScaledUniqueness
import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.JointMeasureLaw

/-! # Joint laws under radial compact containment -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls TopologicalSpace
open scoped ENNReal

/-- A shared measurable measure functional transfers joint laws of stopped
families when their members are radially compact before the horizon. -/
theorem identDistrib_observable_halfBallFamily_of_radial_containment
    {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X] {P : Measure Ω}
    {x y : Ω → X} {μ ν : Ω → Measure ℂ}
    {T U : Ω → ℝ} {Λ Γ : Ω → ℝ → Set ℂ}
    (hxy : IdentDistrib (fun ω => (x ω, μ ω)) (fun ω => (y ω, ν ω)) P P)
    (hμ : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧
      ∃ βm βp, VolumeGrowth (μ ω) (3 / 4) βm βp)
    (hν : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (ν ω) ∧
      ∃ βm βp, VolumeGrowth (ν ω) (3 / 4) βm βp)
    (hΛ : ∀ᵐ ω ∂P, 0 < T ω ∧ IsConeHarmonicBallFamilyOn (μ ω) (Λ ω) (T ω) ∧
      IsStoppedAtHalfBall (Λ ω) (T ω) ∧ ∀ t ∈ Ioo 0 (T ω), ∃ r : ℝ, r < 1 / 2 ∧ Λ ω t ⊆ ball 0 r)
    (hΓ : ∀ᵐ ω ∂P, 0 < U ω ∧ IsConeHarmonicBallFamilyOn (ν ω) (Γ ω) (U ω) ∧
      IsStoppedAtHalfBall (Γ ω) (U ω) ∧ ∀ t ∈ Ioo 0 (U ω), ∃ r : ℝ, r < 1 / 2 ∧ Γ ω t ⊆ ball 0 r) :
    IdentDistrib (fun ω => (x ω, familyProcess (Λ ω) (T ω)))
      (fun ω => (y ω, familyProcess (Γ ω) (U ω))) P P := by
  obtain ⟨F, hF, hFeq⟩ := exists_measurable_halfBallFamily_of_radial_containment
  have hD := hxy.comp (measurable_fst.prodMk (hF.comp measurable_snd))
  have hleft : ∀ᵐ ω ∂P, (x ω, F (μ ω)) = (x ω, familyProcess (Λ ω) (T ω)) := by
    filter_upwards [hμ, hΛ] with ω hm hf
    exact congrArg (Prod.mk (x ω)) (hFeq _ hm.1 hm.2 _ _ hf.1 hf.2.1 hf.2.2.1 hf.2.2.2)
  have hright : ∀ᵐ ω ∂P, (y ω, F (ν ω)) = (y ω, familyProcess (Γ ω) (U ω)) := by
    filter_upwards [hν, hΓ] with ω hm hf
    exact congrArg (Prod.mk (y ω)) (hFeq _ hm.1 hm.2 _ _ hf.1 hf.2.1 hf.2.2.1 hf.2.2.2)
  exact ((IdentDistrib.of_ae_eq hD.aemeasurable_fst hleft).symm.trans hD).trans
    (IdentDistrib.of_ae_eq hD.aemeasurable_snd hright)

/-- The joint field and stopped-family law follows from the two horizon
uniqueness assertions, without a strict-growth hypothesis. -/
theorem IsConeField.identDistrib_rescaledCircleHalfBallFamily_of_unique_horizons
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hcone : IsConeField γ P hC hcirc μ) (h27 : VolumeGrowthStmt)
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (huniq : ConeRescaledHalfBallHorizonUniqueStep) (hscale : QuantumConeScalingInput)
    (hlqg : ConeLQGScalingStep) {b : ℝ} (hb : 0 < b)
    {T U : Ω → ℝ} {Λ Γ : Ω → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, 0 < T ω ∧ IsConeHarmonicBallFamilyOn (μ ω) (Λ ω) (T ω) ∧
      IsStoppedAtHalfBall (Λ ω) (T ω))
    (hΓ : ∀ᵐ ω ∂P, 0 < U ω ∧ IsConeHarmonicBallFamilyOn (μ ω) (Γ ω) (b * U ω) ∧
      IsStoppedAtHalfBall (rescaledFamily (Γ ω) (coneScaleRadius γ (hcirc ω) b) b) (U ω)) :
    IdentDistrib (fun ω => (circleProcess (hcirc ω), familyProcess (Λ ω) (T ω)))
      (fun ω => (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b),
        familyProcess (rescaledFamily (Γ ω) (coneScaleRadius γ (hcirc ω) b) b) (U ω))) P P := by
  have hs := hlqg γ hγ hγ2 Ω P hC hcirc μ hcone b hb
  have hgood : ∀ᵐ ω ∂P,
      IsLocallyFiniteMeasure (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) ∧
      ∃ βm βp, VolumeGrowth (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b)
        (3 / 4) βm βp := by
    filter_upwards [hs, hcone.ae_rescaledVolumeGrowth_inside_unit hγ hγ2 h27 hscale hlqg
      hb (R := (3 / 4 : ℝ)) (by norm_num) (by norm_num)] with ω hω hv
    exact ⟨hω.2.isLocallyFiniteMeasure, hv⟩
  apply identDistrib_observable_halfBallFamily_of_radial_containment
    (hcone.identDistrib_rescaledCircleMeasure hγ hγ2 hscale hlqg hb).symm
    (hcone.ae_volumeGrowth_inside_unit hγ hγ2 h27 (by norm_num)) hgood
  · filter_upwards [hΛ, h24 γ hγ hγ2 Ω P hC hcirc μ hcone] with ω hω hgood
    refine ⟨hω.1, hω.2.1, hω.2.2, ?_⟩
    obtain ⟨T₀, hT₀, Λ₀, hΛ₀, hs₀, hunique⟩ := hgood
    have heq := (hunique (T ω) (Λ ω) hω.1 hω.2.1 hω.2.2).1
    apply radial_containment_of_unique_stopped_family hω.2.1 hω.2.2
    intro S Δ hS hΔ hsΔ
    exact ((hunique S Δ hS hΔ hsΔ).1).trans heq.symm
  · filter_upwards [hΓ, hs, huniq γ hγ hγ2 Ω P hC hcirc μ hcone b hb] with ω hω hR hu
    refine ⟨hω.1, coneHarmonicBallFamilyOnScalingStep (μ ω) (Γ ω) _ b (U ω)
      hR.1 hb hω.2.1, hω.2.2, ?_⟩
    intro t ht
    by_contra h
    push Not at h
    obtain ⟨S, htS, hST⟩ := exists_between ht.2
    have hS : 0 < S := ht.1.trans htS
    have hsS := hω.2.2.restrict_of_early_contact hST.le ⟨ht.1, htS⟩ h
    have hfS : IsConeHarmonicBallFamilyOn (μ ω) (Γ ω) (b * S) :=
      hω.2.1.restrict_time (mul_pos hb hS) (mul_le_mul_of_nonneg_left hST.le hb.le)
    exact (ne_of_lt hST) (hu (U ω) S (Γ ω) (Γ ω) hω.1 hω.2.1 hω.2.2 hS hfS hsS)



/-- Existence of an unscaled family whose rescaling stops at the half disk.
This intermediate assertion makes no uniqueness or measurability claim. -/
def ConeRescaledHalfBallFamilyExistenceStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∀ b : ℝ, 0 < b → ∀ᵐ ω ∂P,
    ∃ (T : ℝ) (Λ : ℝ → Set ℂ), 0 < T ∧
      IsConeHarmonicBallFamilyOn (μ ω) Λ (b * T) ∧
      IsStoppedAtHalfBall (rescaledFamily Λ (coneScaleRadius γ (hcirc ω) b) b) T

/-- The existence part of Lemma 2.5 follows from Lemmas 2.4 and 2.5. -/
theorem coneRescaledHalfBallFamilyExistenceStep_of_lemmas
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt) (h25 : ConeScaleInvarianceUpToFixedTimeStmt) :
    ConeRescaledHalfBallFamilyExistenceStep := by
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
  exact ⟨T₀ ω, Λ₀ ω, hω.1, hω.2.1, hω.2.2.1⟩

/-- Lemma 2.5 follows from existence and uniqueness of the rescaled stopped
family: its joint-law assertion follows from the measurable measure decoder. -/
theorem coneScaleInvarianceUpToFixedTime_of_horizon_steps
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (hex : ConeRescaledHalfBallFamilyExistenceStep)
    (huniq : ConeRescaledHalfBallHorizonUniqueStep)
    (h27 : VolumeGrowthStmt) (hscale : QuantumConeScalingInput)
    (hlqg : ConeLQGScalingStep) : ConeScaleInvarianceUpToFixedTimeStmt := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hcone T Λ hΛ b hb
  have hex' : ∀ᵐ ω ∂P, ∃ y : ℝ × (ℝ → Set ℂ), 0 < y.1 ∧
      IsConeHarmonicBallFamilyOn (μ ω) y.2 (b * y.1) ∧
      IsStoppedAtHalfBall (rescaledFamily y.2 (coneScaleRadius γ (hcirc ω) b) b) y.1 := by
    filter_upwards [hex γ hγ hγ2 Ω P hC hcirc μ hcone b hb] with ω hω
    obtain ⟨S, Γ, hS, hΓ, hs⟩ := hω
    exact ⟨(S, Γ), hS, hΓ, hs⟩
  let x : Ω → ℝ × (ℝ → Set ℂ) := fun ω => Classical.epsilon fun y => 0 < y.1 ∧
    IsConeHarmonicBallFamilyOn (μ ω) y.2 (b * y.1) ∧
    IsStoppedAtHalfBall (rescaledFamily y.2 (coneScaleRadius γ (hcirc ω) b) b) y.1
  have hx : ∀ᵐ ω ∂P, 0 < (x ω).1 ∧
      IsConeHarmonicBallFamilyOn (μ ω) (x ω).2 (b * (x ω).1) ∧
      IsStoppedAtHalfBall (rescaledFamily (x ω).2 (coneScaleRadius γ (hcirc ω) b) b) (x ω).1 := by
    filter_upwards [hex'] with ω hω
    exact Classical.epsilon_spec hω
  refine ⟨fun ω => (x ω).1, fun ω => (x ω).2, ?_, ?_⟩
  · filter_upwards [hx, huniq γ hγ hγ2 Ω P hC hcirc μ hcone b hb] with ω hω hu
    refine ⟨hω.1, hω.2.1, hω.2.2, ?_⟩
    intro S Γ hS hΓ hs
    have heq := hu (x ω).1 S (x ω).2 Γ hω.1 hω.2.1 hω.2.2 hS hΓ hs
    refine ⟨heq, ?_⟩
    have hfg := hω.2.1.eqOn hΓ
    rw [heq, min_self] at hfg
    exact hfg
  · exact (hcone.identDistrib_rescaledCircleHalfBallFamily_of_unique_horizons hγ hγ2
      h27 h24 huniq hscale hlqg hb hΛ hx).map_eq


/-- Under Lemma 2.4 and the volume and scaling inputs, Lemma 2.5 is
exactly the conjunction of rescaled existence and horizon uniqueness. -/
theorem coneScaleInvarianceUpToFixedTime_iff_horizon_steps
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt) (h27 : VolumeGrowthStmt)
    (hscale : QuantumConeScalingInput) (hlqg : ConeLQGScalingStep) :
    ConeScaleInvarianceUpToFixedTimeStmt ↔
      ConeRescaledHalfBallFamilyExistenceStep ∧ ConeRescaledHalfBallHorizonUniqueStep := by
  constructor
  · intro h25
    exact ⟨coneRescaledHalfBallFamilyExistenceStep_of_lemmas h24 h25,
      coneRescaledHalfBallHorizonUniqueStep_of_lemmas h24 h25⟩
  · rintro ⟨hex, huniq⟩
    exact coneScaleInvarianceUpToFixedTime_of_horizon_steps h24 hex huniq h27 hscale hlqg

end MatedCRT
