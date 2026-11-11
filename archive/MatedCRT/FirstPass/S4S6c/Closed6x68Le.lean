import MatedCRT.FirstPass.S4S6c.Closed6x68
import MatedCRT.FirstPass.S4S6c.ShellChainCGRCXLe68
import MatedCRT.FirstPass.S4S6c.CGRCXLeCore68

/-!
# Closed Lemmas 6.7, 6.8, 6.9 from the X counting CG one-test input under `C ≤ CG`

First-pass forms of `firstPass_6_7/8/9_of_hOneX` (Closed6x68X.lean:112-114) with the one-test input
`LICGRCXLe68.ShellOneTestOrderAeCGRCXLeStmt` (`hOneXLe`) and the prevalence input `WindowPrevLeCGStmt` (`hprevLe`, the
residual, open mathematics). The five prevalence inputs `hLit hBM hCC hB1 hμ` of the X forms are replaced by
`hprevLe`, which is their only use: they served only to build the window constant of the chain. The conclusions are those
of the X forms. The `hU` route is `Lemma68ShellTopCGRCXLe.hU_top_cgRCXLe` (ShellChainCGRCXLe68.lean).

Terminology: Armstrong-Kuusi-Mourrat (good annuli, shell order), Duplantier-Sheffield (quantum cone), Berestycki-Powell
(LQG measure), Armitage-Gardiner (balls, Green functions).
-/

open MeasureTheory Filter Topology Metric HarmonicBalls ProbabilityTheory Set
open scoped ENNReal

namespace MatedCRT

/-- **Lemma 6.7, first-pass form under `C ≤ CG`.** As `firstPass_6_7_of_hOneX` (Closed6x68X.lean:112) with
`hprevLe` for `hLit hBM hCC hB1 hμ`, and `hOneXLe` for `hOneX`. -/
theorem firstPass_6_7_of_hOneXLe {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hprevLe : Lemma68CGRCXLe.WindowPrevLeCGStmt)
    (hOneXLe : LICGRCXLe68.ShellOneTestOrderAeCGRCXLeStmt 𝒮) :
    FaithfulConstantOrderLowerBoundStmt 𝒮 :=
  firstPass_6_7_faithful 𝒮
    (Lemma68ShellTopCGRCXLe.hU_top_cgRCXLe (CertifiedReferenceModel.greenKernelLowerBound hCRM)
      (CertifiedReferenceModel.cellSizeEstimate hCRM)
      (CountingExitAlpha68.countingAtExitAlphaStmt_of_firstPass hCRM) hprevLe hOneXLe)

/-- **Lemma 6.8, first-pass form under `C ≤ CG` (localized).** As `firstPass_6_8_of_hOneX`
(Closed6x68X.lean:86) with `hprevLe` for `hLit hBM hCC hB1 hμ`, and `hOneXLe` for `hOneX`. -/
theorem firstPass_6_8_of_hOneXLe {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hprevLe : Lemma68CGRCXLe.WindowPrevLeCGStmt)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hOneXLe : LICGRCXLe68.ShellOneTestOrderAeCGRCXLeStmt 𝒮) :
    FaithfulConstantOrderLowerBoundDivStmt 𝒮 :=
  firstPass_6_8_faithful 𝒮
    (Lemma68ShellTopCGRCXLe.hU_top_cgRCXLe (CertifiedReferenceModel.greenKernelLowerBound hCRM)
      (CertifiedReferenceModel.cellSizeEstimate hCRM)
      (CountingExitAlpha68.countingAtExitAlphaStmt_of_firstPass hCRM) hprevLe hOneXLe)
    (volumeGrowthStmt_of_berestyckiGwynne hBG) (CertifiedReferenceModel.cellSizeEstimate hCRM)

/-- **Lemma 6.9, first-pass form under `C ≤ CG`.** As `firstPass_6_9_of_hOneX` (Closed6x68X.lean:114) with
`hprevLe` for `hLit hBM hCC hB1 hμ`, and `hOneXLe` for `hOneX`. -/
theorem firstPass_6_9_of_hOneXLe {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hprevLe : Lemma68CGRCXLe.WindowPrevLeCGStmt)
    (hOneXLe : LICGRCXLe68.ShellOneTestOrderAeCGRCXLeStmt 𝒮) :
    FaithfulChanceOfBeingAbsorbedStmt 𝒮 :=
  firstPass_6_9_faithful 𝒮
    (Lemma68ShellTopCGRCXLe.hU_top_cgRCXLe (CertifiedReferenceModel.greenKernelLowerBound hCRM)
      (CertifiedReferenceModel.cellSizeEstimate hCRM)
      (CountingExitAlpha68.countingAtExitAlphaStmt_of_firstPass hCRM) hprevLe hOneXLe)

/-! ### Residual forms: the one-test input from `shellOneTestOrderAeCGRCXLe_of_open3` (CGRCXLeCore68.lean). -/

/-- **Lemma 6.7, first-pass form from the residuals under `C ≤ CG`.** As `firstPass_6_7_of_hOneXLe`, with
`hOneXLe` produced by `Lemma68CGRCXLeCore.shellOneTestOrderAeCGRCXLe_of_open3` from the residuals `hTest` (79a), `hGreen`
(75a), `hWalk` (75a G1), `hRad` (77a), `hCtr` (74a); the volume growth `hVG` is a binder. -/
theorem firstPass_6_7_of_residuals {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hprevLe : Lemma68CGRCXLe.WindowPrevLeCGStmt)
    (hVG : VolumeGrowthStmt)
    (hTest : MatedCRT.Lemma68CGResLoc.ShellCGTestEndLoc 𝒮)
    (hGreen : MatedCRT.Lemma68ShellCoreCG.ShellCGResGreen 𝒮)
    (hWalk : MatedCRT.Lemma68ShellCoreCG.ShellCGResWalk 𝒮)
    (hRad : MatedCRT.Lemma68CGRCXG2Core.ShellCGResG2Rad 𝒮)
    (hCtr : MatedCRT.Lemma68CGRCXG2Core.ShellCGResG2Ctr 𝒮) :
    FaithfulConstantOrderLowerBoundStmt 𝒮 :=
  firstPass_6_7_of_hOneXLe hCRM hprevLe
    (Lemma68CGRCXLeCore.shellOneTestOrderAeCGRCXLe_of_open3 hVG hTest hGreen hWalk hRad hCtr)

/-- **Lemma 6.8, first-pass form from the residuals under `C ≤ CG` (localized).** As
`firstPass_6_8_of_hOneXLe`; the volume growth comes from the binder `hBG` (`volumeGrowthStmt_of_berestyckiGwynne`), the
residuals as in `firstPass_6_7_of_residuals`. -/
theorem firstPass_6_8_of_residuals {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hprevLe : Lemma68CGRCXLe.WindowPrevLeCGStmt)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hTest : MatedCRT.Lemma68CGResLoc.ShellCGTestEndLoc 𝒮)
    (hGreen : MatedCRT.Lemma68ShellCoreCG.ShellCGResGreen 𝒮)
    (hWalk : MatedCRT.Lemma68ShellCoreCG.ShellCGResWalk 𝒮)
    (hRad : MatedCRT.Lemma68CGRCXG2Core.ShellCGResG2Rad 𝒮)
    (hCtr : MatedCRT.Lemma68CGRCXG2Core.ShellCGResG2Ctr 𝒮) :
    FaithfulConstantOrderLowerBoundDivStmt 𝒮 :=
  firstPass_6_8_of_hOneXLe hCRM hprevLe hBG
    (Lemma68CGRCXLeCore.shellOneTestOrderAeCGRCXLe_of_open3 (volumeGrowthStmt_of_berestyckiGwynne hBG)
      hTest hGreen hWalk hRad hCtr)

/-- **Lemma 6.9, first-pass form from the residuals under `C ≤ CG`.** As `firstPass_6_9_of_hOneXLe`, with
the residuals and the volume growth `hVG` as in `firstPass_6_7_of_residuals`. -/
theorem firstPass_6_9_of_residuals {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hprevLe : Lemma68CGRCXLe.WindowPrevLeCGStmt)
    (hVG : VolumeGrowthStmt)
    (hTest : MatedCRT.Lemma68CGResLoc.ShellCGTestEndLoc 𝒮)
    (hGreen : MatedCRT.Lemma68ShellCoreCG.ShellCGResGreen 𝒮)
    (hWalk : MatedCRT.Lemma68ShellCoreCG.ShellCGResWalk 𝒮)
    (hRad : MatedCRT.Lemma68CGRCXG2Core.ShellCGResG2Rad 𝒮)
    (hCtr : MatedCRT.Lemma68CGRCXG2Core.ShellCGResG2Ctr 𝒮) :
    FaithfulChanceOfBeingAbsorbedStmt 𝒮 :=
  firstPass_6_9_of_hOneXLe hCRM hprevLe
    (Lemma68CGRCXLeCore.shellOneTestOrderAeCGRCXLe_of_open3 hVG hTest hGreen hWalk hRad hCtr)

end MatedCRT

#print axioms MatedCRT.firstPass_6_7_of_hOneXLe
#print axioms MatedCRT.firstPass_6_8_of_hOneXLe
#print axioms MatedCRT.firstPass_6_9_of_hOneXLe
#print axioms MatedCRT.firstPass_6_7_of_residuals
#print axioms MatedCRT.firstPass_6_8_of_residuals
#print axioms MatedCRT.firstPass_6_9_of_residuals
