import MatedCRT.Defs.Setting
import MatedCRT.Defs.QuantumCone
import MatedCRT.FirstPass.Frozen.S5cSimilarity
import MatedCRT.FirstPass.SLERef.Code

/-!
# First pass: similarity transfer for the reference law

`FPSimilarityTransferCorrected 𝒮` is the similarity transfer of the cone field and the space-filling SLE: independence is imposed between the cone data and the Lebesgue-area representative `ηL`, not between the cone data
and the quantum-area-parametrized curve `η`; both triples are equal in law after the similarity, and the scaling
`η(b ·)` is taken with the quantum-area clock.

Truth-checked: UNSURE for a fixed model (see the docstring of `FPSimilarityTransferCorrected`); its universal
closure over all models does not hold, so it is a per-model hypothesis. Its external content enters only through `SLEReferenceExistsInput`
(`MatedCRT/FirstPass/Frozen/SLERef.lean`).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set

/-- **Corrected similarity transfer for a space-filling SLE model** (a proposition, not an input). For `γ ∈ (0, 2)`, a
quantum cone field `h` with circle average process `circleProcess (hcirc ω)` and quantum area measure `μ ω` (`IsConeField`),
a space-filling SLE `η` of parameter `κ = 16 / γ²` (`IsSLE`) and a measurable Lebesgue-area representative `ηL` of `η`
(`IsLebesgueRepresentative`) which is independent of the cone data, and for every scale `b > 0`, the triple consisting of
the rescaled circle process, the rescaled quantum area measure and the scaled curve `s ↦ r⁻¹ η(b s)` with
`r = coneScaleRadius γ (hcirc ω) b` has the same law as the unscaled triple `(circleProcess (hcirc ω), μ ω, η ω)`.

Independence concerns `ηL`, and the conclusion is an identity in law of the triples built from `η`.

For a fixed model `𝒮` the statement holds for a genuinely calibrated SLE model (or a model calibrated to its normalized
law); it is not automatically discharged for an arbitrary `SpaceFillingSLEModel`, since the model parameter alone supplies
no such fact. -/
def FPSimilarityTransferCorrected (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (𝓕 : MeasurableSpace Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ)
    (η : Ω → ℝ → ℂ)
    (ηL : Ω → C(ℝ, ℂ)),
    @IsConeField Ω mΩ γ P hC hcirc μ →
    @SpaceFillingSLEModel.IsSLE 𝒮 Ω mΩ P 𝓕 (16 / γ ^ 2) η →
    Measurable[mΩ] (fun ω => (circleProcess (hcirc ω), μ ω)) →
    Measurable[mΩ] ηL →
    (∀ᵐ ω ∂P, IsLebesgueRepresentative (η ω) (ηL ω)) →
    IndepFun (fun ω => (circleProcess (hcirc ω), μ ω)) ηL P →
    (∀ᵐ ω ∂P, IsAreaParametrized (μ ω) (η ω)) →
    ∀ b : ℝ, 0 < b →
    @IdentDistrib Ω Ω _ mΩ mΩ _
      (fun ω =>
        (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b),
         FPScaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b,
         fun s : ℝ => ((coneScaleRadius γ (hcirc ω) b : ℝ) : ℂ)⁻¹ * η ω (b * s)))
      (fun ω => (circleProcess (hcirc ω), μ ω, η ω))
      P P

end MatedCRT
