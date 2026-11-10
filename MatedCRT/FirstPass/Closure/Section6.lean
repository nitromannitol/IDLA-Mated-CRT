import MatedCRT.FirstPass.S5S6S7
import MatedCRT.FirstPass.Closure.SLEPackage

/-!
# Closed results, Section 6 (task fp-Closure-counted-results, worker z1)

Closed: 6.4 (`closed_6_4`, good annulus prevalence) and 6.5 (`closed_6_5`, annulus hit) are aliases (no SLE model).
6.10 (`closed_6_10`) is stated for a model `𝒮` with normalized law `ν`, with `GreenKernelLowerBoundStmt` and
`ExitTimeUpperBoundStmt` from the package. Not closed: 6.1 (needs Lemma 5.1, not counted).
-/

open MeasureTheory

namespace MatedCRT

/-- Lemma 6.4 (good prevalence of annuli), closed. Hypotheses: frozen whole-plane Props. -/
alias closed_6_4 := firstPass_6_4

/-- Lemma 6.5 (annulus hit), closed. Hypotheses: frozen whole-plane Props. -/
alias closed_6_5 := firstPass_6_5

/-- Lemma 6.10 (iterative bound), closed for a model `𝒮` with normalized law `ν`. -/
theorem closed_6_10 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hνC : SLEReferenceInput ν)
    (_hνF : SLEFrozenReferenceInput ν) (hLaw : HasNormalizedSLELaw 𝒮 ν) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction) : IterativeBoundStmt 𝒮 :=
  firstPass_6_10 (𝒮 := 𝒮) (slePkg_greenKernelLower hνC hLaw) h27 h28 h29 (slePkg_exitTimeUpper hνC hLaw) h0 h2 hV hR

end MatedCRT
