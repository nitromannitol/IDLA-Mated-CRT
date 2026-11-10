import MatedCRT.FirstPass.S3i.LensStep
import MatedCRT.FirstPass.S3i.ExitAlmostSure
import MatedCRT.FirstPass.S3i.QuenchedBoundsCorrected

/-!
# Corrected Lemma 3.6 through the BE/lens route, closed (fp-S3i-3-6-closed; binder swap fp-S6r-shortwindow-derived step 0)

`firstPass_3_6_annealed_closed` (LensStep.lean:60) concludes `CorrectedHarmonicConvergenceStmt 𝒮 ∧
CorrectedHarmonicSameWalkAnnealedStmt 𝒮` from the frozen inputs `h211`, `h28`, `hm`, `hexc`, `h32`, `hBE` and the
Lemma 7 input `hQB : QuenchedBoundsOnGoodStmt` (LensStep.lean:29).

The Lemma 7 input is now supplied by the corrected Lemma 7 of z12, `quenchedBoundsOnGoodStmt_of_exit`
(`QuenchedBoundsCorrected.lean`, committed 416cf0c), whose a.s.-exit hypothesis is discharged by the z10 theorem
`srwLaw_vExitTime_lt_top_fp36` (`ExitAlmostSure.lean`, committed 8acffb3). The former named binders `hQBc` and `hexit`
are removed. The remaining binders are the frozen and literature inputs `h211`, `h28`, `hm`, `hexc`, `h32`, `hBE`.

Terminology: quenched law `srwLaw` and exit time `vExitTime` (Armstrong-Kuusi-Mourrat); lens of the boundary cell
(Berestycki-Powell, boundary estimate of GMS (3.31)).
-/

namespace MatedCRT
namespace FirstPass36

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- **Corrected Lemma 3.6 through the BE/lens route, closed.** The conclusion is
`firstPass_3_6_annealed_closed`'s, that is `CorrectedHarmonicConvergenceStmt 𝒮 ∧ CorrectedHarmonicSameWalkAnnealedStmt 𝒮`
(S3i/Statement.lean:39, the corrected numbered Lemma 3.6), not the Draft conjunction `CorrectedLemma36Stmt`
(Draft/Section3HarmonicCorrected.lean:96), whose second conjunct is the retired pointwise rate. -/
theorem firstPass_3_6_closed {𝒮 : SpaceFillingSLEModel} (h211 : RandomWalkToLBMStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) (hBE : FrozenOneSidedBoundaryContinuity 𝒮) :
    CorrectedHarmonicConvergenceStmt 𝒮 ∧ CorrectedHarmonicSameWalkAnnealedStmt 𝒮 :=
  firstPass_3_6_annealed_closed h211 h28 hm hexc h32 hBE
    (quenchedBoundsOnGoodStmt_of_exit srwLaw_vExitTime_lt_top_fp36)

#print axioms MatedCRT.FirstPass36.firstPass_3_6_closed

end FirstPass36
end MatedCRT
