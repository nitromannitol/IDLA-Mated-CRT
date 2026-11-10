import MatedCRT.FirstPass.S5S6S7
import MatedCRT.FirstPass.SLERef.Certified

/-!
# Closed results, Section 7 (task fp-Closure-counted-results, fp-Closure-round3, worker z1)

Closed for a model `𝒮` with certified reference model `hC : CertifiedReferenceModel ν 𝒮` (chat 186): 7.2 (`closed_7_2`,
corrected form; inputs `hC.greenKernelLowerBound` and `hC.cellSizeEstimate`) and 7.3 (`closed_7_3`, no inputs).
Not closed: 7.1 (needs Lemma 2.3 and Lemma 4.1).
-/

open MeasureTheory

namespace MatedCRT

/-- Lemma 7.2 (mass bound for the odometer above scale), corrected form, for a model `𝒮` with certified reference model
`hC`. -/
theorem closed_7_2 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hC : CertifiedReferenceModel ν 𝒮) :
    MassBoundOdometerAboveScaleStmt 𝒮 :=
  firstPass_7_2_corrected (𝒮 := 𝒮) hC.greenKernelLowerBound hC.cellSizeEstimate

/-- Lemma 7.3 (odometer bound by mass). No further hypotheses. -/
theorem closed_7_3 {𝒮 : SpaceFillingSLEModel} : OdometerBoundMassStmt 𝒮 :=
  firstPass_7_3 (𝒮 := 𝒮)

end MatedCRT
