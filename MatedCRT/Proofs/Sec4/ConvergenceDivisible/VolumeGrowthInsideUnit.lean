import MatedCRT.Draft.Section2
import MatedCRT.Proofs.Infra.Setting
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.LeastMeasurableOfVolumeGrowth
import HarmonicBalls.Steps.Sec2.VolumeGrowth
import HarmonicBalls.Defs.Obstacle

/-! # Almost sure volume growth inside the unit ball -/

namespace MatedCRT

open MeasureTheory Filter Metric Set HarmonicBalls

/-- Polynomial ball-mass estimates at two exponents give almost sure
volume growth with any positive slack in the exponents. -/
theorem ae_volumeGrowth_of_poly_ballMass {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {μ : Ω → Measure ℂ} {R a b βplus βminus : ℝ}
    (ha : 0 < a) (hab : a < βplus) (hb : 0 < b) (hba : βminus < b)
    (hpoly : PolyHighProb P (ballMassBoundEvent μ R βplus βminus)) :
    ∀ᵐ ω ∂P, VolumeGrowth (μ ω) R b a := by
  obtain ⟨r₁, hr₁, hwin⟩ := ballMassBoundEvent_window μ ha hab hb hba
  have hpoly' := (hpoly.inter (hpoly.comp_mul (by norm_num : (0 : ℝ) < 2⁻¹))).mono_of_small hr₁ hwin
  filter_upwards [hpoly'.ae_eventually_dyadic] with ω hω
  obtain ⟨K, hK⟩ := eventually_atTop.1 hω
  refine ⟨hb, ha, (2 : ℝ)⁻¹ ^ K, by positivity, fun r hr hrK z hz => ?_⟩
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near_of_lt_one hr
    (hrK.le.trans (pow_le_one₀ (by norm_num) (by norm_num))) (by norm_num : (0 : ℝ) < 2⁻¹)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hkK : K ≤ k := by
    by_contra hlt
    have h' : k + 1 ≤ K := by omega
    have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num) h'
    linarith
  refine hK k hkK r ?_ hk2 z hz
  rw [pow_succ] at hk1
  linarith

/-- Lemma 2.7 implies almost sure volume growth on every fixed ball
strictly inside the unit ball. -/
theorem MatedCRTEnv.IsValid.ae_volumeGrowth_inside_unit
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) {R : ℝ} (hR : R < 1) :
    ∀ᵐ ω ∂S.P, ∃ βminus βplus, VolumeGrowth (S.μ ω) R βminus βplus := by
  let A : ℝ := (2 - γ) ^ 2 / 2
  let B : ℝ := (2 + γ) ^ 2 / 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hbound := h27 γ hγ hγ2 (A / 2) (B + 1) (by positivity)
    (by dsimp [A] at *; linarith) (by dsimp [B]; linarith)
    Ω S.P S.hC S.hcirc S.μ hS.isConeField
  have hpoly : PolyHighProb S.P (ballMassBoundEvent S.μ R (A / 2) (B + 1)) := by
    refine hbound.mono_of_small (sub_pos.2 hR) ?_
    intro δ hδ hδR ω hω z hz
    exact hω z (ball_subset_ball (by linarith) hz)
  filter_upwards [ae_volumeGrowth_of_poly_ballMass (a := A / 4) (b := B + 2)
    (by positivity) (by linarith) (by positivity) (by linarith) hpoly] with ω hω
  exact ⟨_, _, hω⟩

/-- Lemma 2.7 implies pointwise measurability of the continuum least
supersolution on each ball strictly inside the unit ball. -/
theorem MatedCRTEnv.IsValid.aemeasurable_leastSupersolution_inside_unit
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) {R t : ℝ} {z x : ℂ} (hR : 0 < R) (hR1 : R < 1)
    (ht : 0 < t) (hz : z ∈ ball (0 : ℂ) R) (hx : x ∈ closedBall (0 : ℂ) R) :
    AEMeasurable (fun ω => leastSupersolution (S.μ ω) R z t x) S.P :=
  hS.aemeasurable_leastSupersolution_of_volumeGrowth R t z x hR ht hz hx
    (hS.ae_volumeGrowth_inside_unit hγ hγ2 h27 hR1)

end MatedCRT
