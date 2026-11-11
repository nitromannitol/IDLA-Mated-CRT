import MatedCRT.FirstPass.SLERef.Code
import MatedCRT.FirstPass.SLERef.Similarity
import MatedCRT.FirstPass.SLERef.Reference
import MatedCRT.FirstPass.Frozen.SLERef
import MatedCRT.FirstPass.SLERef.Extended
import MatedCRT.FirstPass.SLERef.Certified

/-!
# First pass: consumers of the reference law of whole-plane space-filling SLE

Projections from the reference certificates to the numbered results they cite and to the two unresolved frozen inputs.
Nothing here constructs an SLE law. The frozen existence input is `SLEReferenceExistsInput`
(`MatedCRT/FirstPass/Frozen/SLERef.lean`); the certificates are `SLEReferenceInput`, `SLEReferenceWithSimilarityInput` and
`SLEFrozenReferenceInput` (`MatedCRT/FirstPass/SLERef/Reference.lean`). The firstPass theorems are unchanged: they keep their
frozen hypotheses, which the projections below supply for the same law `ν`.
-/

namespace MatedCRT

open MeasureTheory

/-- A model whose normalized law is a reference law `ν` satisfies the five cited numbered results. The extra
hypothesis for a firstPass theorem that takes a cited Stmt is the pair `(hν : SLEReferenceInput ν)`,
`(hLaw : HasNormalizedSLELaw 𝒮 ν)`, with this projection replacing the Stmt. -/
theorem slecited_of_referenceLaw {ν : ℝ → Measure SLEPathCode} (hν : SLEReferenceInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : SLECitedInputs 𝒮 :=
  hν.2 𝒮 hLaw

/-- From the frozen existence input: some law `ν` is such that every model with normalized law `ν` satisfies the five
cited numbered results. The law is chosen once; the target model must then have normalized law exactly that `ν`. -/
theorem exists_slecited_of_referenceExists (hE : SLEReferenceExistsInput) :
    ∃ ν : ℝ → Measure SLEPathCode, ∀ 𝒮 : SpaceFillingSLEModel,
      HasNormalizedSLELaw 𝒮 ν → SLECitedInputs 𝒮 := by
  obtain ⟨ν, hν⟩ := hE
  exact ⟨ν, hν.1.2⟩

/-- From the frozen existence input: one law `ν` for all three clauses at once, namely the five cited numbered results, the
corrected similarity transfer and the fixed-time truncated quenched laws. Every target model must have normalized law exactly
this `ν`. -/
theorem exists_reference_of_referenceExists (hE : SLEReferenceExistsInput) :
    ∃ ν : ℝ → Measure SLEPathCode, ∀ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν →
      SLECitedInputs 𝒮 ∧ FPSimilarityTransferCorrected 𝒮 ∧ FrozenTruncatedQuenchedLawsFixedTime 𝒮 := by
  obtain ⟨ν, hν⟩ := hE
  exact ⟨ν, fun 𝒮 hLaw => ⟨hν.1.2 𝒮 hLaw, (hν.2 𝒮 hLaw).1, (hν.2 𝒮 hLaw).2⟩⟩

/-- From the frozen existence input: the minimal frozen package of the frozen package for the
same law `ν` as the reference certificate. -/
theorem exists_frozenReference_of_referenceExists (hE : SLEReferenceExistsInput) :
    ∃ ν : ℝ → Measure SLEPathCode, SLEFrozenReferenceInput ν := by
  obtain ⟨ν, hν⟩ := hE
  exact ⟨ν, sleFrozenReference_of_withSimilarity hν⟩

end MatedCRT
