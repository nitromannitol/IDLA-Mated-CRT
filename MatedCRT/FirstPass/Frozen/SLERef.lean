import MatedCRT.FirstPass.SLERef.Reference
import MatedCRT.FirstPass.Frozen.S3S4

/-!
# First pass: frozen external input for the reference law of whole-plane space-filling SLE (task fp-SLERef-reference-law;
corrected by task fp-SLERef2-certify)

`SLEReferenceExistsInput` is the frozen literature input for the reference law of whole-plane space-filling SLE. It is a
proposition about laws of curves and of the cone field, and it does not identify the SLE law intrinsically. No Lean object
constructs SLE here, and no Lean proof of the literature transfer is given. The propositions it uses are in
`MatedCRT/FirstPass/SLERef/Reference.lean`, `MatedCRT/FirstPass/SLERef/Similarity.lean` and
`MatedCRT/FirstPass/SLERef/Code.lean`.

This file also gives the derivations of the two firstPass consumers from the reference package for one chosen law `ν`:
`FrozenDiscreteHolderContinuityCorrected 𝒮` and `FrozenTruncatedQuenchedLawsFixedTime 𝒮`, for every model `𝒮` with normalized
law `ν`, and a non-vacuity statement for the reference model.

Sources of the truth discussion: `notes/fp-gaps/CHATGPT-sleref-truth.md` §1.3 and §2.1,
`notes/fp-gaps/CHATGPT-fpsimilarity-truth.md` §5–§7, `notes/fp-gaps/CHATGPT-idla-sle-frozen-7.md` §§1–4 and §8.
-/

namespace MatedCRT

open MeasureTheory

/-- FIRST-PASS FROZEN. Reference existence and uniform transfer for one chosen law family `ν : ℝ → Measure SLEPathCode`.
The proposition is `∃ ν, SLEReferenceWithSimilarityInput ν`: some `ν` is the normalized law of a space-filling SLE model
realized, for every `γ ∈ (0, 2)`, by valid environments on `ℝ`, and every model with normalized law `ν` satisfies (a) the five
cited numbered results of the paper, with the corrected Lemma 3.2 (`SLECitedInputs`; Theorem 2.11, Lemmas 2.14, 2.16, 2.18
and corrected Lemma 3.2), (b) the corrected similarity transfer `FPSimilarityTransferCorrected`, and (c) the fixed-time
truncated quenched laws `FrozenTruncatedQuenchedLawsFixedTime`.

PENDING TRUTH CHECK (operator): the truth of this proposition has not been checked by the operator. It is recorded as TRUE
under the certified reference law by `notes/fp-gaps/CHATGPT-idla-sle-frozen-7.md` (for the truncated laws, §4) and
`notes/fp-gaps/CHATGPT-fpsimilarity-truth.md` §7 (for the similarity clause); the corrected Lemma 3.2 is UNRESOLVED for an
unconstrained model.

This certificate does not intrinsically characterize the SLE law or impose closure properties on the raw predicate
`𝒮.IsSLE`. In particular, the existence part alone does not prove `HasNormalizedSLELaw 𝒮 ν` for a target model chosen
beforehand; the target must receive that hypothesis for the same `ν`, or a package containing both the certificate and the
target's calibration to it. Clause (c) quantifies over the discrete occupation of `MatedCRTEnv` and is not a statement about
SLE laws alone; this is flagged for the operator.

The law family `ν` is chosen once, inside this existential; every consumer of the clauses above must use that same `ν`. -/
def SLEReferenceExistsInput : Prop :=
  ∃ ν : ℝ → Measure SLEPathCode, SLEReferenceWithSimilarityInput ν

/-- The corrected Lemma 3.2 for a model with normalized law `ν`, from the frozen reference package: the consumer
`FrozenDiscreteHolderContinuityCorrected 𝒮` of the firstPass theorems. -/
theorem frozenDiscreteHolder_of_frozenReferenceLaw {ν : ℝ → Measure SLEPathCode} (hν : SLEFrozenReferenceInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : FrozenDiscreteHolderContinuityCorrected 𝒮 :=
  (hν.2 𝒮 hLaw).1

/-- The fixed-time truncated quenched laws for a model with normalized law `ν`, from the frozen reference package: the
consumer `FrozenTruncatedQuenchedLawsFixedTime 𝒮` of the firstPass theorems. -/
theorem frozenTruncatedQuenched_of_frozenReferenceLaw {ν : ℝ → Measure SLEPathCode} (hν : SLEFrozenReferenceInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : FrozenTruncatedQuenchedLawsFixedTime 𝒮 :=
  (hν.2 𝒮 hLaw).2

/-- Non-vacuity of the frozen reference package: some space-filling SLE model `𝒮` with normalized law `ν` satisfies both
frozen estimates, so the firstPass hypotheses `FrozenDiscreteHolderContinuityCorrected 𝒮` and
`FrozenTruncatedQuenchedLawsFixedTime 𝒮` are realized by the reference model. -/
theorem exists_model_of_frozenReferenceLaw {ν : ℝ → Measure SLEPathCode} (hν : SLEFrozenReferenceInput ν) :
    ∃ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν ∧
      FrozenDiscreteHolderContinuityCorrected 𝒮 ∧ FrozenTruncatedQuenchedLawsFixedTime 𝒮 := by
  obtain ⟨⟨𝒮ref, hL, _⟩, hall⟩ := hν
  exact ⟨𝒮ref, hL, (hall 𝒮ref hL).1, (hall 𝒮ref hL).2⟩

end MatedCRT
