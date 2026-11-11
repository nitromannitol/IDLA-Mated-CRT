import MatedCRT.FirstPass.S5c.FieldRoute
import MatedCRT.FirstPass.S5c.TestIntegralAE
import MatedCRT.FirstPass.S5c.HmeasFamily
import MatedCRT.FirstPass.S5c.ScaleEntry
import MatedCRT.FirstPass.Frozen.S4S6c

/-!
# FIRST PASS, Lemma 5.3: the environment inputs of the 5.3 route

For a valid environment `S` (`MatedCRTEnv.IsValid`) this file derives from the structure fields the inputs that the
fixed-index margin (`fixedIndexMargin_compact_ae`, ScaleEntry.lean) and the family null-measurability
(`nullMeasurableSet_subset_family`, HmeasFamily.lean) need. No new frozen input is introduced; the only frozen
input is `FrozenLQGMeasureFieldMeasurable` (Frozen/S4S6c.lean), used for the AE form of the test integrals.

* `env_fieldSigma_le`: the field σ-algebra lies in the ambient σ-algebra (`IsQuantumCone.measurable_pairing`).
* `env_ae_mass_finite`: almost surely `μ_h(B̄_R) < ∞` for each real `R` (the γ-LQG measure is Radon, `IsLQGLimit`,
  which is the content of `IsLQGMeasure` in the `IsValid` field `isLQGMeasure`).
* `env_aemeasurable_test`: the test integrals `ω ↦ ∫ φ dμ_h` are AE-measurable for continuous compactly supported `φ`.
* `env_ae_open_monotone`: an almost surely cone harmonic ball family is almost surely open and increasing
  (`IsHarmonicBall`, `SatisfiesHarmonicBallConditions.monotoneOn`).
-/

namespace MatedCRT.S5c

open MeasureTheory Filter Set Metric Topology HarmonicBalls

/-- The field σ-algebra `σ(h)` of a valid environment is contained in the ambient σ-algebra. -/
theorem env_fieldSigma_le {Ω : Type} [mΩ : MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) : S.fieldSigma ≤ mΩ :=
  fieldSigma_le_of_pairing_measurable S.hC (fun φ hφ => hS.isQuantumCone.measurable_pairing φ hφ)

/-- Local finiteness of the LQG measure on balls, almost surely: the γ-LQG measure is a Radon measure. -/
theorem env_ae_mass_finite {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) (R : ℝ) :
    ∀ᵐ ω ∂S.P, S.μ ω (closedBall (0 : ℂ) R) < ⊤ := by
  have h : ∀ᵐ ω ∂S.P, IsLQGLimit γ (S.hcirc ω) (S.μ ω) := hS.isLQGMeasure
  filter_upwards [h] with ω hω
  have := hω.isLocallyFiniteMeasure
  exact (isCompact_closedBall (0 : ℂ) R).measure_lt_top

/-- The test integrals of the LQG measure of a valid environment are AE-measurable (the AE form of the test-integral
measurability, from the frozen field-measurable version `FrozenLQGMeasureFieldMeasurable` of `μ_h`). -/
theorem env_aemeasurable_test {Ω : Type} [mΩ : MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hF : FrozenLQGMeasureFieldMeasurable 𝒮) (hγ0 : 0 < γ) (hγ2 : γ < 2) (S : MatedCRTEnv Ω)
    (hS : S.IsValid 𝒮 γ) :
    ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ → AEMeasurable (fun ω => ∫ x, φ x ∂(S.μ ω)) S.P := by
  intro φ hφ hsupp
  obtain ⟨g, hg, hμg⟩ := hF γ hγ0 hγ2 Ω S hS
  obtain ⟨R, hR⟩ := (hsupp.isCompact.isBounded).subset_closedBall (0 : ℂ)
  exact aemeasurable_integral_of_measurable_version (env_fieldSigma_le S hS) hg hμg
    (env_ae_mass_finite S hS R) hφ hR

/-- An almost surely cone harmonic ball family is almost surely open at every positive time and increasing. -/
theorem env_ae_open_monotone {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {μ : Ω → Measure ℂ}
    {Λ : Ω → ℝ → Set ℂ} (hΛ : ∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω)) :
    ∀ᵐ ω ∂P, (∀ t : ℝ, 0 < t → IsOpen (Λ ω t)) ∧ MonotoneOn (Λ ω) (Ioi 0) :=
  hΛ.mono fun _ hω => ⟨fun t ht => (hω.1 t ht).1, hω.2.1.monotoneOn⟩

/-- Null measurability of the rational-disc inclusions `ratDisc x ⊆ Λ_t` for a valid environment: the input
`hmeas` of `fixedIndexMargin_compact_ae`, from `nullMeasurableSet_subset_family`. -/
theorem env_hmeas_ratDisc {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic) (hF3 : FrozenDiskGreenNonnegCont)
    (hG : FrozenGreenDiscPole) (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (hmeas : ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ → AEMeasurable (fun ω => ∫ x, φ x ∂(S.μ ω)) S.P)
    {Λ : Ω → ℝ → Set ℂ} (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) :
    ∀ (x : RatDiscIndex) (t : ℝ), 0 < t → NullMeasurableSet {ω | ratDisc x ⊆ Λ ω t} S.P := by
  have := hS.isProbabilityMeasure
  exact fun x t ht => nullMeasurableSet_subset_family hF1 hF3 hG hΛ (fun R => env_ae_mass_finite S hS R) hmeas ht
    (isCompact_closedBall _ _)

/-- **Statement (a) of three-inputs section 1, for a valid environment**: the fixed-index margin on compact subsets
of `Λ_t`, from the frozen inputs `FrozenLQGMeasureFieldMeasurable`, `FPStrongMinimumPrinciple` and the frozen
Lusin/Green inputs of HmeasFamily, and the scaling identity `hscale` (A4; see docs/campaign/COUNTED.md). -/
theorem fixedIndexMargin_compact_env {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hF : FrozenLQGMeasureFieldMeasurable 𝒮) (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF3 : FrozenDiskGreenNonnegCont) (hG : FrozenGreenDiscPole) (hmin : FPStrongMinimumPrinciple)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) (Λ : Ω → ℝ → Set ℂ)
    (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (hscale : ∀ b t : ℝ, 0 < b → 0 < t → S.P (newEntranceEvent Λ (b * t)) = S.P (newEntranceEvent Λ t))
    {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) :
    ∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ → ∀ K : Set ℂ, IsCompact K → K ⊆ Λ ω t →
      ∃ β : ℝ, 0 < β ∧
        ∀ x ∈ K, β ≤ leastSupersolution (S.μ ω) ρ 0 t x - 2 * leastSupersolution (S.μ ω) ρ 0 (t / 2) x :=
  have := hS.isProbabilityMeasure
  fixedIndexMargin_compact_ae S.P S.μ Λ hmin hΛ (env_ae_open_monotone hΛ)
    (env_hmeas_ratDisc hF1 hF3 hG S hS (env_aemeasurable_test hF hγ0 hγ2 S hS) hΛ) hscale hρ ht

end MatedCRT.S5c
