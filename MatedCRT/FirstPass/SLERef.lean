import MatedCRT.FirstPass.SLERef.Code
import MatedCRT.FirstPass.SLERef.Reference
import MatedCRT.FirstPass.Frozen.SLERef

/-!
# First pass: consumers of the reference law of whole-plane space-filling SLE (task fp-SLERef-reference-law, worker z10)

Projections from the reference certificate to the five cited numbered results. Nothing here constructs an SLE law.
The frozen existence input is `SLEReferenceExistsInput` (`MatedCRT/FirstPass/Frozen/SLERef.lean`), and the
certificate is `SLEReferenceInput` (`MatedCRT/FirstPass/SLERef/Reference.lean`).
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
  exact ⟨ν, hν.2⟩

end MatedCRT
