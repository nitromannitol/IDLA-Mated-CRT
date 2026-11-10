import MatedCRT.Defs.Setting
import MatedCRT.Defs.QuantumCone

/-!
# FIRST PASS frozen input: similarity transfer of the cone field and the whole-plane SLE (steps2-r3 Section 9)

Exactly the form of `notes/fp-gaps/CHATGPT-similarity-transfer.md`, which the operator ruled TRUE with a scope correction
(22:25 UTC): the scaling `b` is deterministic and the joint `(h, η)` is scaled. This is a literature fact about the quantum cone
and the whole-plane space-filling SLE, not a statement about this paper's clusters, odometers, harmonic balls or IDLA processes.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- The scaled area measure `μ_{h^{(b)}}(A) = b⁻¹ μ_h(R_b A)`, in the Lean form of `rescaledMeasure`
(Steps/Sec2/ConeScaleInvarianceUpToFixedTime.lean:27): the pushforward of `μ` by `x ↦ R⁻¹ x`, times `b⁻¹`.
The image-set formula `μ.map (x ↦ R⁻¹ x) (A) = μ(R • A)` holds only for `R ≠ 0` (for `R = 0` the Lean inverse `0⁻¹ = 0`
collapses the map, so the identity with `μ_h(R_b A)` fails); the source's `R_b` is a.s. positive, a point to be kept
explicit in the input (operator truth check 20:04 UTC, notes/fp-gaps/CHATGPT-frozen-truth-2005.md). -/
noncomputable def FPScaledMeasure (μ : Measure ℂ) (R b : ℝ) : Measure ℂ :=
  ENNReal.ofReal b⁻¹ • μ.map fun x => (R : ℂ)⁻¹ * x

/-- RETIRED (FALSE, ChatGPT 02:21 UTC; corrected form by lead li's team). **FIRST-PASS FROZEN.** Similarity transfer of the whole-plane quantum cone `h` and the independent space-filling SLE_{16/γ²}
`η` (steps2-r3 Section 9; CHATGPT-similarity-transfer.md). For `γ ∈ (0,2)`, a quantum cone `h` (`IsConeField`) and a whole-plane
space-filling SLE `η` (`IsSLE` with the σ-algebra `𝓕` of the field, so `η` is independent of `𝓕`), with the circle averages and
`μ_h` `𝓕`-measurable: for every deterministic `b > 0`, with `R_b = sup {r > 0 : h_r(0) + Q log r = γ⁻¹ log b}`
(`coneScaleRadius`), the triple (circle averages of `h^{(b)} = h(R_b ·) + Q log R_b - γ⁻¹ log b`, `μ_{h^{(b)}}`,
`η^{(b)}(s) = R_b⁻¹ η(b s)`) has the same law as (circle averages of `h`, `μ_h`, `η`).
Source: Duplantier–Miller–Sheffield, arXiv:1409.7055v4, Proposition 4.13(i); the joint version is Berestycki–Gwynne,
arXiv:2003.10320v2, Lemma 2.3 and §6.4, (6.52). Truth check FALSE (ChatGPT, 02:21 UTC; notes/fp-gaps/CHATGPT-fpsimilarity-truth.md, opening verdict).
Used by: StoppedLayerPotentialStep (Proofs/Sec5/StoppedSurplusSteps.lean:68)
and firstPass_5_1 (stopped clause). Note: `Measure.map` of a non-measurable map is `0`; the equality is meant for the random
triples the source asserts to be random variables. -/
def FPSimilarityTransfer (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) (𝓕 : MeasurableSpace Ω) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (η : Ω → ℝ → ℂ),
    IsConeField γ P hC hcirc μ →
    @SpaceFillingSLEModel.IsSLE 𝒮 Ω _ P 𝓕 (16 / γ ^ 2) η →
    Measurable[𝓕] (fun ω => (circleProcess (hcirc ω), μ ω)) →
    ∀ b : ℝ, 0 < b →
    P.map (fun ω => (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b),
        FPScaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b,
        fun s : ℝ => (((coneScaleRadius γ (hcirc ω) b : ℝ) : ℂ))⁻¹ * η ω (b * s))) =
      P.map (fun ω => (circleProcess (hcirc ω), μ ω, η ω))

end MatedCRT
