import MatedCRT.FirstPass.S4S6c.Closed6x68
import MatedCRT.FirstPass.S4S6c.ShellChainCGRCX68

/-!
# Closed Lemmas 6.7, 6.8, 6.9 and 6.x from the X counting CG one-test input

Copies of `closed_6_7_hU_cgRC`, `closed_6_8_hU_cgRC`, `closed_6_9_hU_cgRC`, `closed_6_x_hU_cgRC` (Closed6x68.lean:306-360)
and of `firstPass_6_7/8/9_of_hOne` (Closed6x68.lean:365-400), with the producer `hOne : ShellOneTestOrderAeCGRCStmt 𝒮`
replaced by `hOneX : LICGRCX68.ShellOneTestOrderAeCGRCXStmt 𝒮`: the same one-test bound, with the extra exit clause at the
cell radius `rhoCell68 ρ` (`PolyHighProb` and the almost sure premise). Nothing else changes; the chain is in
`ShellChainCGRCX68.lean` (`Lemma68ShellTopCGRCX.hU_top_cgRCX`).

Terminology: Armstrong-Kuusi-Mourrat (good annuli, shell order), Duplantier-Sheffield (quantum cone, LQG measure),
Berestycki-Powell (LQG measure), Armitage-Gardiner (balls, Green functions).
-/

open MeasureTheory Filter Topology Metric HarmonicBalls ProbabilityTheory Set
open scoped ENNReal

namespace MatedCRT

/-- **Lemma 6.7 (faithful header), closed from the X counting CG one-test input.** As `closed_6_7_hU_cgRC`. -/
theorem closed_6_7_hU_cgRCX {𝒮 : SpaceFillingSLEModel}
    (hG : GreenKernelLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hK : Lemma68Guard10.CountingAtExitAlphaStmt 𝒮)
    (hOneX : LICGRCX68.ShellOneTestOrderAeCGRCXStmt 𝒮) :
    FaithfulConstantOrderLowerBoundStmt 𝒮 :=
  firstPass_6_7_faithful 𝒮
    (Lemma68ShellTopCGRCX.hU_top_cgRCX hG h28 hK hLit hBM hCC hB1 hμ hOneX)

/-- **Lemma 6.8 (faithful header, localized form), X counting CG route.** As `closed_6_8_hU_cgRC`. -/
theorem closed_6_8_hU_cgRCX {𝒮 : SpaceFillingSLEModel}
    (hG : GreenKernelLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hK : Lemma68Guard10.CountingAtExitAlphaStmt 𝒮)
    (hOneX : LICGRCX68.ShellOneTestOrderAeCGRCXStmt 𝒮) :
    FaithfulConstantOrderLowerBoundDivStmt 𝒮 :=
  firstPass_6_8_faithful 𝒮
    (Lemma68ShellTopCGRCX.hU_top_cgRCX hG h28 hK hLit hBM hCC hB1 hμ hOneX)
    (volumeGrowthStmt_of_berestyckiGwynne hBG) h28

/-- **Lemma 6.9 (faithful header), X counting CG route.** As `closed_6_9_hU_cgRC`. -/
theorem closed_6_9_hU_cgRCX {𝒮 : SpaceFillingSLEModel}
    (hG : GreenKernelLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hK : Lemma68Guard10.CountingAtExitAlphaStmt 𝒮)
    (hOneX : LICGRCX68.ShellOneTestOrderAeCGRCXStmt 𝒮) :
    FaithfulChanceOfBeingAbsorbedStmt 𝒮 :=
  firstPass_6_9_faithful 𝒮
    (Lemma68ShellTopCGRCX.hU_top_cgRCX hG h28 hK hLit hBM hCC hB1 hμ hOneX)

/-- **Lemma 6.x, uniform constant-order lower bound (hU), X counting CG route.** As `closed_6_x_hU_cgRC`. -/
theorem closed_6_x_hU_cgRCX {𝒮 : SpaceFillingSLEModel}
    (hG : GreenKernelLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hK : Lemma68Guard10.CountingAtExitAlphaStmt 𝒮)
    (hOneX : LICGRCX68.ShellOneTestOrderAeCGRCXStmt 𝒮) :
    UniformConstantOrderLowerBoundStmt 𝒮 :=
  Lemma68ShellTopCGRCX.hU_top_cgRCX hG h28 hK hLit hBM hCC hB1 hμ hOneX

/-! ### First-pass forms from the certified reference model, X counting CG route. -/

/-- **Lemma 6.7, first-pass form of the X counting CG route.** As `firstPass_6_7_of_hOne` with `hOneX`. -/
theorem firstPass_6_7_of_hOneX {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hOneX : LICGRCX68.ShellOneTestOrderAeCGRCXStmt 𝒮) :
    FaithfulConstantOrderLowerBoundStmt 𝒮 :=
  closed_6_7_hU_cgRCX (CertifiedReferenceModel.greenKernelLowerBound hCRM)
    (CertifiedReferenceModel.cellSizeEstimate hCRM) hLit hBM hCC hB1 hμ
    (CountingExitAlpha68.countingAtExitAlphaStmt_of_firstPass hCRM) hOneX

/-- **Lemma 6.8, first-pass form of the X counting CG route (localized).** As `firstPass_6_8_of_hOne` with `hOneX`. -/
theorem firstPass_6_8_of_hOneX {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hOneX : LICGRCX68.ShellOneTestOrderAeCGRCXStmt 𝒮) :
    FaithfulConstantOrderLowerBoundDivStmt 𝒮 :=
  closed_6_8_hU_cgRCX (CertifiedReferenceModel.greenKernelLowerBound hCRM)
    (CertifiedReferenceModel.cellSizeEstimate hCRM) hLit hBM hCC hB1 hμ hBG
    (CountingExitAlpha68.countingAtExitAlphaStmt_of_firstPass hCRM) hOneX

/-- **Lemma 6.9, first-pass form of the X counting CG route.** As `firstPass_6_9_of_hOne` with `hOneX`. -/
theorem firstPass_6_9_of_hOneX {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hOneX : LICGRCX68.ShellOneTestOrderAeCGRCXStmt 𝒮) :
    FaithfulChanceOfBeingAbsorbedStmt 𝒮 :=
  closed_6_9_hU_cgRCX (CertifiedReferenceModel.greenKernelLowerBound hCRM)
    (CertifiedReferenceModel.cellSizeEstimate hCRM) hLit hBM hCC hB1 hμ
    (CountingExitAlpha68.countingAtExitAlphaStmt_of_firstPass hCRM) hOneX

end MatedCRT

#print axioms MatedCRT.firstPass_6_7_of_hOneX
#print axioms MatedCRT.firstPass_6_8_of_hOneX
#print axioms MatedCRT.firstPass_6_9_of_hOneX
