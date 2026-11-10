import MatedCRT.FirstPass.S4S6c.Closed6x68
import MatedCRT.FirstPass.S4S6c.ShellChainCGRCXLe68

/-!
# Closed Lemmas 6.7, 6.8, 6.9 from the X counting CG one-test input under `C ≤ CG` (fp-S4S6c-chain-le, request 80a)

First-pass forms of `firstPass_6_7/8/9_of_hOneX` (Closed6x68X.lean:112-114) with the one-test input
`LICGRCXLe68.ShellOneTestOrderAeCGRCXLeStmt` (`hOneXLe`) and the prevalence input `WindowPrevLeCGStmt` (`hprevLe`, the
residual of request 80a, open mathematics). The five prevalence inputs `hLit hBM hCC hB1 hμ` of the X forms are replaced by
`hprevLe`, which is their only use: they served only to build the window constant of the chain. The conclusions are those
of the X forms. The `hU` route is `Lemma68ShellTopCGRCXLe.hU_top_cgRCXLe` (ShellChainCGRCXLe68.lean).

Terminology: Armstrong-Kuusi-Mourrat (good annuli, shell order), Duplantier-Sheffield (quantum cone), Berestycki-Powell
(LQG measure), Armitage-Gardiner (balls, Green functions).
-/

open MeasureTheory Filter Topology Metric HarmonicBalls ProbabilityTheory Set
open scoped ENNReal

namespace MatedCRT

/-- **Lemma 6.7, first-pass form under `C ≤ CG` (request 80a).** As `firstPass_6_7_of_hOneX` (Closed6x68X.lean:112) with
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

/-- **Lemma 6.8, first-pass form under `C ≤ CG` (localized, request 80a).** As `firstPass_6_8_of_hOneX`
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

/-- **Lemma 6.9, first-pass form under `C ≤ CG` (request 80a).** As `firstPass_6_9_of_hOneX` (Closed6x68X.lean:114) with
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

end MatedCRT

#print axioms MatedCRT.firstPass_6_7_of_hOneXLe
#print axioms MatedCRT.firstPass_6_8_of_hOneXLe
#print axioms MatedCRT.firstPass_6_9_of_hOneXLe
