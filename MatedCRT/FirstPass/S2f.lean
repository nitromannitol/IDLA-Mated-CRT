import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.JointMeasureLaw
import MatedCRT.FirstPass.S2e

/-!
# First pass: the measurable good set of the cone families

Reduction of `ConeFamilyAEMeasurableStep` (Theorem 2.3 measurability) and of its rescaled conjunct
`ConeRescaledHalfBallClosureInsideStep` to ONE named step, `ConeClosureGoodMeasureLawStep`: a measurable set of
measures of full law on which the closure containment holds for every stopped family. The step is a named hypothesis (see docs/campaign/COUNTED.md); it is a statement about this paper's harmonic balls.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls ProbabilityTheory
open scoped ENNReal

/-- **Named hypothesis (see docs/campaign/COUNTED.md).** Closure containment of the cone families on a measurable
set of full law: for every cone field there is a measurable set `G` of measures such that every `ν ∈ G` has the closure
property of `ConeHalfBallClosureInsideStep` (every family on `ν` stopped at `T` has `closure (Λ t) ⊆ B_{1/2}` for
`0 < t < T`), and `μ ω ∈ G` almost surely. `ConeHalfBallClosureInsideStep` (proved, `FirstPass/S2d.lean`) gives only the
almost sure statement; the measurability of the good set is what the law transfer to the rescaled measures needs (coanalytic good local support, Borel subset of full measure). -/
def ConeClosureGoodMeasureLawStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
    ∃ G : Set (Measure ℂ), MeasurableSet G ∧
      (∀ ν ∈ G, ∀ (T : ℝ) (Λ : ℝ → Set ℂ), IsConeHarmonicBallFamilyOn ν Λ T → IsStoppedAtHalfBall Λ T →
        ∀ t ∈ Ioo 0 T, closure (Λ t) ⊆ ball (0 : ℂ) (1 / 2)) ∧
      ∀ᵐ ω ∂P, μ ω ∈ G

/-- The good-measure step gives the closure containment of `ConeHalfBallClosureInsideStep` for the field itself. -/
theorem coneHalfBallClosureInsideStep_of_goodMeasureLaw (hG : ConeClosureGoodMeasureLawStep) :
    ConeHalfBallClosureInsideStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hcone
  obtain ⟨G, _, hGgood, hGae⟩ := hG γ hγ hγ2 Ω P hC hcirc μ hcone
  filter_upwards [hGae] with ω hω
  intro T Λ hΛ hst t ht
  exact hGgood _ hω T Λ hΛ hst t ht

/-- **Rescaled closure from the good-measure law.** The rescaled measures
`rescaledMeasure (μ ω) (R_b ω) b` have the law of `μ` (second marginal of
`IsConeField.identDistrib_rescaledCircleMeasure`), so they lie in the measurable full-law set `G` almost surely, and the
closure containment on `G` gives `ConeRescaledHalfBallClosureInsideStep`. -/
theorem coneRescaledHalfBallClosureInsideStep_of_goodMeasureLaw
    (hscale : QuantumConeScalingInput) (hlqg : ConeLQGScalingStep)
    (hG : ConeClosureGoodMeasureLawStep) : ConeRescaledHalfBallClosureInsideStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hcone b hb
  obtain ⟨G, hGm, hGgood, hGae⟩ := hG γ hγ hγ2 Ω P hC hcirc μ hcone
  have hid := IsConeField.identDistrib_rescaledCircleMeasure hγ hγ2 hcone hscale hlqg hb
  have hνμ : IdentDistrib (fun ω => rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b)
      (fun ω => μ ω) P P := hid.comp measurable_snd
  have hbad : P ((fun ω => rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) ⁻¹' Gᶜ) = 0 := by
    rw [hνμ.measure_mem_eq hGm.compl]
    exact ae_iff.1 hGae
  have hgood : ∀ᵐ ω ∂P, rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b ∈ G :=
    ae_iff.2 hbad
  filter_upwards [hgood] with ω hω
  intro T Γ hΓ hst t ht
  exact hGgood _ hω T Γ hΓ hst t ht

/-- **Conditional reduction of `ConeFamilyAEMeasurableStep`.** Both conjuncts follow from the volume growth
inputs of `firstPass_coneFamilyAEMeasurableStep_of_rescaledClosure` and the single step
`ConeClosureGoodMeasureLawStep`; the closure containments (unrescaled and rescaled) are derived from it. -/
theorem firstPass_coneFamilyAEMeasurableStep_of_goodMeasureLaw
    (h27 : VolumeGrowthStmt) (hscale : QuantumConeScalingInput) (hlqg : ConeLQGScalingStep)
    (hvgood : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ → ∀ b : ℝ, 0 < b →
      ∀ᵐ ω ∂P, ∃ βminus βplus, VolumeGrowth
        (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) (3 / 4) βminus βplus)
    (hG : ConeClosureGoodMeasureLawStep) : ConeFamilyAEMeasurableStep :=
  firstPass_coneFamilyAEMeasurableStep_of_rescaledClosure h27 hscale hlqg hvgood
    (coneHalfBallClosureInsideStep_of_goodMeasureLaw hG)
    (coneRescaledHalfBallClosureInsideStep_of_goodMeasureLaw hscale hlqg hG)

end MatedCRT
