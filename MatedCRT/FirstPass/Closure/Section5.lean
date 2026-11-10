import MatedCRT.FirstPass.S5S6S7
import MatedCRT.FirstPass.Closure.SLEPackage

/-!
# Closed results, Section 5 (task fp-Closure-counted-results, worker z1)

Closed for a model `𝒮` with normalized law `ν`: 5.2 (`closed_5_2`), 5.4 (`closed_5_4`, `GreenKernelLowerBoundStmt` from the
package). Not closed: 5.3 (gaps G9 and 4.1), 5.1 is not in the counted set.
-/

open MeasureTheory

namespace MatedCRT

/-- Lemma 5.2 (general IDLA lower bound), for a model with normalized law `ν`. -/
theorem closed_5_2 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (_hνC : SLEReferenceInput ν)
    (_hνF : SLEFrozenReferenceInput ν) (_hLaw : HasNormalizedSLELaw 𝒮 ν) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) : GeneralIDLALowerBoundStmt 𝒮 :=
  firstPass_5_2 (𝒮 := 𝒮) h27 h28

/-- Lemma 5.4 (L lower bound), for a model with normalized law `ν`. -/
theorem closed_5_4 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hνC : SLEReferenceInput ν)
    (_hνF : SLEFrozenReferenceInput ν) (hLaw : HasNormalizedSLELaw 𝒮 ν) (h215 : GreenFunctionCrudeBoundStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) : LLowerBoundStmt 𝒮 :=
  firstPass_5_4 (𝒮 := 𝒮) h215 (slePkg_greenKernelLower hνC hLaw) h29

end MatedCRT
