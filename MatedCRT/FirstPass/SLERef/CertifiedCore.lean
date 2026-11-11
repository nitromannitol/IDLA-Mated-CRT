import MatedCRT.FirstPass.S5qe
import MatedCRT.FirstPass.S3t.BLEnvelopeClosure

/-!
# The certified reference model from its core (audit finding B5 of `OPUS-AUDIT-R1`)

`CertifiedReferenceModelCore ν 𝒮` (`MatedCRT/FirstPass/S5qe.lean:33`) is `CertifiedReferenceModel ν 𝒮`
(`MatedCRT/FirstPass/SLERef/Certified.lean:54`) without conjunct 17, `FrozenTruncatedQuenchedLawsFixedTime 𝒮`
(`Certified.lean:71`). The conjunct is supplied by `MatedCRT.TruncatedLaws.truncatedQuenchedLawsFixedTime_of_inputs`
(`MatedCRT/FirstPass/S3t/BLEnvelopeClosure.lean:43`) from conjuncts 3, 5 and 11 of the core, together with the exit
input `BrownianOutwardExcursionAtExitStep` (Mörters–Peres, Brownian Motion, Theorems 2.16 and 2.7). That exit input is
the one residual hypothesis of `certifiedReferenceModel_of_core`.
-/

namespace MatedCRT

open MeasureTheory

/-- The certified reference model from its core. Conjunct 17 is `truncatedQuenchedLawsFixedTime_of_inputs` applied to
the core conjuncts 11 (`RandomWalkToLBMStmt`), 5 (`CellSizeEstimateStmt`) and 3 (`MepsScalingInput`), and to the
Brownian exit input `hBM`. All other conjuncts are the core ones, in the same order. -/
theorem certifiedReferenceModel_of_core {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hcore : CertifiedReferenceModelCore ν 𝒮) (hBM : BrownianOutwardExcursionAtExitStep) :
    CertifiedReferenceModel ν 𝒮 := by
  unfold CertifiedReferenceModelCore at hcore
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := hcore
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    TruncatedLaws.truncatedQuenchedLawsFixedTime_of_inputs h11 h5 h3 hBM, h17⟩

end MatedCRT
