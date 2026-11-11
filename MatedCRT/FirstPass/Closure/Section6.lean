import MatedCRT.FirstPass.S5S6S7
import MatedCRT.FirstPass.S6p
import MatedCRT.FirstPass.S6q
import MatedCRT.FirstPass.SLERef.Certified

/-!
# Closed results, Section 6

Closed: 6.4 (`closed_6_4`, corrected [C18] uniform form, `firstPass_6_4_uniform`) and 6.5 (`closed_6_5`, corrected [C5]
uniform form `C = C(p)`, `firstPass_6_5_uniform`, S6q.lean) are aliases (no SLE model).
6.10 (`closed_6_10`) is stated for a model `𝒮` with certified reference model `hC : CertifiedReferenceModel ν 𝒮`;
its inputs `GreenKernelLowerBoundStmt`, `CellSizeEstimateStmt`, `CountingMeasureConvergenceStmt` and
`ExitTimeUpperBoundStmt` are projections of `hC`. Not closed: 6.1 (needs Lemma 5.1, not counted).
-/

open MeasureTheory

namespace MatedCRT

/-- Lemma 6.4 (good prevalence of annuli), corrected form [C18] with `C = C(γ, c₀)`: `GoodAnnulusPrevalenceUniformStmt`,
from `firstPass_6_4_uniform` (S6p.lean). Hypotheses: the frozen whole-plane Props and the EXTERNAL / frozen inputs of
`firstPass_6_4_uniform` (the same four hypotheses as the printed `firstPass_6_4`). -/
alias closed_6_4 := MatedCRT.FirstPass64.firstPass_6_4_uniform

/-- Lemma 6.5 (annulus hit), corrected uniform form `AnnulusHitUniformStmt` (`C = C(p)`), closed, from
`firstPass_6_5_uniform` (S6q.lean). Hypotheses: frozen whole-plane Props (the three inputs of `firstPass_6_5`). -/
alias closed_6_5 := MatedCRT.FirstPass64.firstPass_6_5_uniform

/-- Lemma 6.10 (iterative bound), closed for a model `𝒮` with certified reference model `hC`. -/
theorem closed_6_10 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hC : CertifiedReferenceModel ν 𝒮)
    (h27 : VolumeGrowthStmt) (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail) (hR : FPConeMeanZeroRestriction) : IterativeBoundStmt 𝒮 :=
  firstPass_6_10 (𝒮 := 𝒮) hC.greenKernelLowerBound h27 hC.cellSizeEstimate hC.countingMeasureConvergence
    hC.exitTimeUpperBound h0 h2 hV hR

end MatedCRT
