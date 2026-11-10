import MatedCRT.FirstPass.SLERef.Code
import MatedCRT.FirstPass.SLERef.Similarity
import MatedCRT.Draft.Section2
import MatedCRT.Steps.Sec3.DiscretePotentialTightness
import MatedCRT.FirstPass.Frozen.S3S4b

/-!
# First pass: reference propositions for the space-filling SLE law (task fp-SLERef-reference-law, worker z10;
certificate corrected by task fp-SLERef2-certify)

The five numbered results of the paper that are cited from the literature and whose statements quantify over valid
environments through the abstract predicate `SpaceFillingSLEModel.IsSLE`: Theorem 2.11 (`RandomWalkToLBMStmt`),
Lemma 2.14 (`GreenKernelUpperBoundStmt`), Lemma 2.16 (`GreenKernelLowerBoundStmt`), Lemma 2.18
(`ExitTimeUpperBoundStmt`) and the corrected Lemma 3.2 (`DiscreteHolderContinuityCorrectedStep`). The printed
`DiscreteHolderContinuityStmt` is FALSE (docs/campaign/CORRECTED-FORMS.md, entry 3.2) and is not used here.
This module is not imported by the Draft modules, so there is no cycle.

`SLEReferenceInput ν` says that `ν` is a reference law: it is the normalized law of some model with valid reference
environments on `ℝ`, and every model with that normalized law satisfies the five cited statements.
`SLEReferenceWithSimilarityInput ν` adds, for the same `ν`, the corrected similarity transfer and the truncated quenched
laws. `SLEFrozenReferenceInput ν` is the minimal package of `notes/fp-gaps/CHATGPT-idla-sle-frozen-7.md` §8 for the two
unresolved frozen inputs. The frozen existence proposition `SLEReferenceExistsInput` is in
`MatedCRT/FirstPass/Frozen/SLERef.lean`. Nothing here asserts that a family `ν` is realized by an SLE; that is the
frozen input. Analytic transfer (the universal clauses) is kept apart from reference-model non-vacuity (a model with
normalized law `ν` and valid reference environments).
-/

namespace MatedCRT

open MeasureTheory

/-- The five cited numbered results (2.11, 2.14, 2.16, 2.18, and the corrected Lemma 3.2) for one space-filling SLE model
`𝒮`. The fifth conjunct is `DiscreteHolderContinuityCorrectedStep`, which replaces the printed Lemma 3.2. -/
def SLECitedInputs (𝒮 : SpaceFillingSLEModel) : Prop :=
  RandomWalkToLBMStmt 𝒮 ∧
  GreenKernelUpperBoundStmt 𝒮 ∧
  GreenKernelLowerBoundStmt 𝒮 ∧
  ExitTimeUpperBoundStmt 𝒮 ∧
  DiscreteHolderContinuityCorrectedStep 𝒮

/-- The model `𝒮` is realized by valid environments with parameter `γ` on the standard Borel space `ℝ`, for every
`γ ∈ (0, 2)`. The choice of `ℝ` is a sampling-space convention for the reference only. -/
def HasReferenceEnvironments (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∃ S : MatedCRTEnv ℝ, S.IsValid 𝒮 γ

/-- `ν` is a reference law for the five cited results: some model with the normalized law `ν` has valid reference
environments, and every model with the normalized law `ν` satisfies the five cited statements. SUPERSEDED (chat 186). The earlier FALSE label rested on the universal quantification of `SLECitedInputs` over the `IsSLE` semantics, field and graph of every model with normalized law `ν`; universal model quantification alone is not a refutation (truth check 2026-11-10). Non-vacuity of the reference model is the separate frozen input `SLEReferenceExistsInput` (UNSURE). Superseded by `CertifiedReferenceModel` (`MatedCRT/FirstPass/SLERef/Certified.lean`); kept unchanged. -/
def SLEReferenceInput (ν : ℝ → Measure SLEPathCode) : Prop :=
  (∃ 𝒮ref : SpaceFillingSLEModel,
    HasNormalizedSLELaw 𝒮ref ν ∧ HasReferenceEnvironments 𝒮ref) ∧
  ∀ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν → SLECitedInputs 𝒮

/-- `ν` is a reference law with the similarity and truncated-laws clauses, for the same `ν`: every model with normalized
law `ν` satisfies the corrected similarity transfer `FPSimilarityTransferCorrected` and the fixed-time truncated quenched
laws `FrozenTruncatedQuenchedLawsFixedTime`. Source: `notes/fp-gaps/CHATGPT-sleref-truth.md` §2.1 and
`notes/fp-gaps/CHATGPT-idla-sle-frozen-7.md` §4. SUPERSEDED (chat 186). The second conjunct quantifies `FPSimilarityTransferCorrected` and `FrozenTruncatedQuenchedLawsFixedTime` over all models with normalized law `ν` and over valid environments `S : MatedCRTEnv Ω` with `S.IsValid 𝒮 γ`. The universal closure of `FPSimilarityTransferCorrected` over all space-filling models is FALSE (truth check 2026-11-10); whether the restriction to normalized law `ν` suffices is not decided here. Superseded by `CertifiedReferenceModel` (`MatedCRT/FirstPass/SLERef/Certified.lean`); kept unchanged. -/
def SLEReferenceWithSimilarityInput (ν : ℝ → Measure SLEPathCode) : Prop :=
  SLEReferenceInput ν ∧
  ∀ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν →
    FPSimilarityTransferCorrected 𝒮 ∧ FrozenTruncatedQuenchedLawsFixedTime 𝒮

/-- The two unresolved estimates for one model: the corrected Lemma 3.2 (`DiscreteHolderContinuityCorrectedStep`, the body
of `FrozenDiscreteHolderContinuityCorrected`) and the fixed-time truncated quenched laws. -/
def SLEFrozenEstimates (𝒮 : SpaceFillingSLEModel) : Prop :=
  DiscreteHolderContinuityCorrectedStep 𝒮 ∧ FrozenTruncatedQuenchedLawsFixedTime 𝒮

/-- The minimal reference package of `notes/fp-gaps/CHATGPT-idla-sle-frozen-7.md` §8, for one law family `ν`: some model
with normalized law `ν` has valid reference environments, and every model with normalized law `ν` satisfies
`SLEFrozenEstimates`. The consumers `FrozenDiscreteHolderContinuityCorrected` and `FrozenTruncatedQuenchedLawsFixedTime`
are derived from it in `MatedCRT/FirstPass/Frozen/SLERef.lean`. SUPERSEDED (chat 186). The second conjunct `SLEFrozenEstimates` quantifies `DiscreteHolderContinuityCorrectedStep` and `FrozenTruncatedQuenchedLawsFixedTime` over the `IsSLE` semantics of every model with normalized law `ν`; universal model quantification alone is not a refutation (truth check 2026-11-10). Superseded by `CertifiedReferenceModel` (`MatedCRT/FirstPass/SLERef/Certified.lean`); kept unchanged. -/
def SLEFrozenReferenceInput (ν : ℝ → Measure SLEPathCode) : Prop :=
  (∃ 𝒮ref : SpaceFillingSLEModel,
    HasNormalizedSLELaw 𝒮ref ν ∧ HasReferenceEnvironments 𝒮ref) ∧
  ∀ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν → SLEFrozenEstimates 𝒮

/-- The similarity clause and the truncated-laws clause, for the law `ν` of a reference certificate, give the minimal
frozen package for the same `ν`. -/
theorem sleFrozenReference_of_withSimilarity {ν : ℝ → Measure SLEPathCode}
    (hν : SLEReferenceWithSimilarityInput ν) : SLEFrozenReferenceInput ν := by
  unfold SLEFrozenReferenceInput SLEFrozenEstimates
  refine ⟨hν.1.1, fun 𝒮 hLaw => ?_⟩
  exact ⟨(hν.1.2 𝒮 hLaw).2.2.2.2, (hν.2 𝒮 hLaw).2⟩

/-- Projection: the corrected similarity transfer for every model with normalized law `ν`. -/
theorem similarity_of_referenceLaw {ν : ℝ → Measure SLEPathCode} (hν : SLEReferenceWithSimilarityInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : FPSimilarityTransferCorrected 𝒮 :=
  (hν.2 𝒮 hLaw).1

/-- Projection: the fixed-time truncated quenched laws for every model with normalized law `ν`. -/
theorem truncatedLaws_of_referenceLaw {ν : ℝ → Measure SLEPathCode} (hν : SLEReferenceWithSimilarityInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : FrozenTruncatedQuenchedLawsFixedTime 𝒮 :=
  (hν.2 𝒮 hLaw).2

end MatedCRT
