import MatedCRT.FirstPass.S4S6c.Closed6x68
import MatedCRT.FirstPass.S4S6c.ShellChainCGRCY68

/-!
# First-pass forms of Lemmas 6.7, 6.8, 6.9 from the Y counting CG one-test input (fp-S4S6c-chain-y, lead li 20:05 UTC)

Analogues of `firstPass_6_7/8/9_of_hOneX` (Closed6x68X.lean:74-114) with the one-test producer
`LICGRCY68.ShellOneTestOrderAeCGRCYStmt` (`hOneY`). The conclusions are those of the X forms; the binders are those of the X
forms with `hOneX` replaced by `hOneY`, plus ONE extra named input `hVol : Lemma68CGRCY.FieldVolCutoffStmt 𝒮`
(the field-measurable volume cutoff of Codex Q2a step 5, q2's `VolCutoffField68.lean`, not yet landed). The radius
guard `VolReady68` of `hOneY` is supplied by the chain from `hVol` (ShellChainCGRCY68.lean, `hU_top_cgRCY`).

No `C ≤ CG` premise anywhere (Codex Q4: `WindowPrevLeCGStmt` is false). The Green exponent `ωG` is supplied by the mesh
`CountingMeshEventsHiStmt` (`countingMeshEventsHi_of_draft`).
-/

open MeasureTheory Filter Topology Metric HarmonicBalls ProbabilityTheory Set
open scoped ENNReal

namespace MatedCRT

/-- **Lemma 6.7, first-pass form of the Y counting CG route.** As `firstPass_6_7_of_hOneX`, with `hOneY` and `hVol`. -/
theorem firstPass_6_7_of_hOneY {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hVol : Lemma68CGRCY.FieldVolCutoffStmt 𝒮)
    (hOneY : LICGRCY68.ShellOneTestOrderAeCGRCYStmt 𝒮) :
    FaithfulConstantOrderLowerBoundStmt 𝒮 :=
  firstPass_6_7_faithful 𝒮
    (Lemma68ShellTopCGRCY.hU_top_cgRCY (CertifiedReferenceModel.greenKernelLowerBound hCRM)
      (CertifiedReferenceModel.cellSizeEstimate hCRM) (CountingExitAlpha68.countingAtExitAlphaStmt_of_firstPass hCRM)
      hLit hBM hCC hB1 hμ hVol hOneY)

/-- **Lemma 6.8, first-pass form of the Y counting CG route.** As `firstPass_6_8_of_hOneX`, with `hOneY` and `hVol`;
the volume growth is `volumeGrowthStmt_of_berestyckiGwynne hBG`. -/
theorem firstPass_6_8_of_hOneY {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hVol : Lemma68CGRCY.FieldVolCutoffStmt 𝒮)
    (hOneY : LICGRCY68.ShellOneTestOrderAeCGRCYStmt 𝒮) :
    FaithfulConstantOrderLowerBoundDivStmt 𝒮 :=
  firstPass_6_8_faithful 𝒮
    (Lemma68ShellTopCGRCY.hU_top_cgRCY (CertifiedReferenceModel.greenKernelLowerBound hCRM)
      (CertifiedReferenceModel.cellSizeEstimate hCRM) (CountingExitAlpha68.countingAtExitAlphaStmt_of_firstPass hCRM)
      hLit hBM hCC hB1 hμ hVol hOneY)
    (volumeGrowthStmt_of_berestyckiGwynne hBG) (CertifiedReferenceModel.cellSizeEstimate hCRM)

/-- **Lemma 6.9, first-pass form of the Y counting CG route.** As `firstPass_6_9_of_hOneX`, with `hOneY` and `hVol`. -/
theorem firstPass_6_9_of_hOneY {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hVol : Lemma68CGRCY.FieldVolCutoffStmt 𝒮)
    (hOneY : LICGRCY68.ShellOneTestOrderAeCGRCYStmt 𝒮) :
    FaithfulChanceOfBeingAbsorbedStmt 𝒮 :=
  firstPass_6_9_faithful 𝒮
    (Lemma68ShellTopCGRCY.hU_top_cgRCY (CertifiedReferenceModel.greenKernelLowerBound hCRM)
      (CertifiedReferenceModel.cellSizeEstimate hCRM) (CountingExitAlpha68.countingAtExitAlphaStmt_of_firstPass hCRM)
      hLit hBM hCC hB1 hμ hVol hOneY)

end MatedCRT

#print axioms MatedCRT.firstPass_6_7_of_hOneY
#print axioms MatedCRT.firstPass_6_8_of_hOneY
#print axioms MatedCRT.firstPass_6_9_of_hOneY
