import MatedCRT.FirstPass.S4S6c.GoodAnnulusMeas
import MatedCRT.FirstPass.S4S6c.BallMassLowerAE
import MatedCRT.Proofs.Measurability.LQGMeasureField

/-!
# Environment-level inputs for a valid environment

For a valid environment `S : MatedCRTEnv Ω` (`S.IsValid 𝒮 γ`, Defs/Setting.lean:141) the LQG measure `S.μ` is almost surely
equal to a `S.fieldSigma`-measurable random measure. This removes the frozen input `FrozenLQGMeasureFieldMeasurable`
(FirstPass/Frozen/S4S6c.lean:44) from the mass and good-radius steps: the proved theorem
`MatedCRT.lqgMeasureFieldMeasurableStep` (Proofs/Measurability/LQGMeasureField.lean:75) supplies it.

* `exists_fieldMeasurable_mu`: the field-measurable version of `S.μ`.
* `ballMass_lower_env`: eq (8) (`BallMassLowerAE.ballMass_lower_of_ae`) for a valid environment, from the polynomial
  mass hypothesis (the first conjunct of Draft 2.7 VolumeGrowthStmt, Draft/Section2.lean:121, passed as `hlow`).
* `cover_polyHighProb_env`: the polynomial bound of the good-annulus cover events of `S.μ` from Draft 6.4
  (`GoodAnnulusPrevalenceStmt`), with `IsConeField` read off `S.IsValid` (`isProbabilityMeasure`, `isQuantumCone`,
  `isLQGMeasure`).
* `goodAnnulusCover_env`: the field-measurable cutoff of eq (9) for the valid environment (from `goodAnnulusCover_dyadic_ae`).

Terminology: LQG measure (Duplantier-Sheffield), good annuli (Berestycki-Powell), mass lower bound (Armstrong-Kuusi-Mourrat).
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace MatedCRT

namespace EnvInputs68

/-- The LQG measure of a valid environment is almost surely equal to a field-measurable random measure. -/
theorem exists_fieldMeasurable_mu {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    ∃ g : Ω → Measure ℂ, Measurable[S.fieldSigma] g ∧ ∀ᵐ ω ∂S.P, S.μ ω = g ω := by
  obtain ⟨μ', hμ', hae⟩ := LQGMeasureField.lqgMeasureFieldMeasurableStep 𝒮 γ hγ hγ2 Ω S hS
  exact ⟨μ', hμ', hae.mono fun ω h => h.symm⟩

/-- **Lemma 2, eq (8)** for a valid environment: the ball masses of `S.μ` are bounded below by `(t/4)^b` for all centres in
`closedBall 0 ρ` and all small radii, on a field-measurable cutoff `tStar`, almost surely. -/
theorem ballMass_lower_env {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {ρ ρ₁ b : ℝ} (hρ : 0 < ρ) (hρρ₁ : ρ < ρ₁) (hρ₁ : ρ₁ < 1) (hb : 0 < b)
    (hlow : HarmonicBalls.PolyHighProb S.P fun δ =>
      {ω | ∀ z ∈ Metric.ball (0 : ℂ) (1 - δ), ENNReal.ofReal (δ ^ b) ≤ S.μ ω (Metric.ball z δ)}) :
    ∃ tStar : Ω → ℝ, Measurable[S.fieldSigma] tStar ∧ ∀ᵐ ω ∂S.P, 0 < tStar ω ∧
      ∀ y ∈ closedBall (0 : ℂ) ρ, ∀ t : ℝ, 0 < t → t < tStar ω →
        ENNReal.ofReal ((t / 4) ^ b) ≤ S.μ ω (Metric.ball y t) := by
  have := hS.isProbabilityMeasure
  exact BallMassLowerAE.ballMass_lower_of_ae S.μ (exists_fieldMeasurable_mu hγ hγ2 S hS) hρ hρρ₁ hρ₁ hb hlow

/-- The polynomial bound of the good-annulus cover events of a valid environment (Draft 6.4, `GoodAnnulusPrevalenceStmt`,
read through `GoodRadiusCover.cover_polyHighProb_of_prevalence`). -/
theorem cover_polyHighProb_env {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hprev : GoodAnnulusPrevalenceStmt)
    (hγ : 0 < γ) (hγ2 : γ < 2) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₀' : c₀ < 1 / 5)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    ∃ C : ℝ, 0 < C ∧ HarmonicBalls.PolyHighProb S.P (fun δ => GoodRadiusCover.GoodAnnulusCoverEvent S.μ ρ c₀ C δ) := by
  obtain ⟨C, hC, h⟩ := GoodRadiusCover.cover_polyHighProb_of_prevalence hprev hγ hγ2 hρ hρ1 hc₀ hc₀'
  have hcone : IsConeField γ S.P S.hC S.hcirc S.μ := by
    unfold IsConeField
    exact ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩
  exact ⟨C, hC, h Ω S.P S.hC S.hcirc S.μ hcone⟩

end EnvInputs68

end MatedCRT
