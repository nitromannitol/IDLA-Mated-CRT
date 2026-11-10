import MatedCRT.FirstPass.S5S6S7
import MatedCRT.FirstPass.Closure.SLEPackage

/-!
# Closed results, Section 7 (task fp-Closure-counted-results, worker z1)

Closed for a model `𝒮` with normalized law `ν`: 7.2 (`closed_7_2`, corrected form; `GreenKernelLowerBoundStmt` from the
package) and 7.3 (`closed_7_3`). Not closed: 7.1 (needs Lemma 2.3 and Lemma 4.1).
-/

open MeasureTheory

namespace MatedCRT

/-- Lemma 7.2 (mass bound for the odometer above scale), corrected form, for a model with normalized law `ν`. -/
theorem closed_7_2 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hνC : SLEReferenceInput ν)
    (_hνF : SLEFrozenReferenceInput ν) (hLaw : HasNormalizedSLELaw 𝒮 ν) (h28 : CellSizeEstimateStmt 𝒮) :
    MassBoundOdometerAboveScaleStmt 𝒮 :=
  firstPass_7_2_corrected (𝒮 := 𝒮) (slePkg_greenKernelLower hνC hLaw) h28

/-- Lemma 7.3 (odometer bound by mass), for a model with normalized law `ν`. No further hypotheses. -/
theorem closed_7_3 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (_hνC : SLEReferenceInput ν)
    (_hνF : SLEFrozenReferenceInput ν) (_hLaw : HasNormalizedSLELaw 𝒮 ν) : OdometerBoundMassStmt 𝒮 :=
  firstPass_7_3 (𝒮 := 𝒮)

end MatedCRT
