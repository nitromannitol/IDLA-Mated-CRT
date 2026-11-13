import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.HolderGoodEvent
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.SameWalkAssembly
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.PathFunctionalStep
import MatedCRT.FirstPass.Frozen.S3S4
import MatedCRT.FirstPass.S3e.HolderGoodEventCorrected

/-!
# First-pass corrected Lemma 3.6

The convergence part of corrected Lemma 3.6 of `paper/idla_mated_crt-corrected.tex` ([C13],
`lemma:convergence-of-harmonic-functions`) is `CorrectedHarmonicConvergenceStmt 𝒮`
(`Draft/Section3HarmonicCorrected.lean`). The old `firstPass_3_6` (`FirstPass/S3S4.lean`) concludes the obsolete
`ConvergenceHarmonicFunctionsStmt` and is left unchanged.

* `firstPass_3_6_convergence` proves the first conjunct from Draft statements of other numbered results
  (Lemma 2.8, Lemma 2.11, Lemma 3.2 in its Draft form), the External `MepsScalingInput`, and the FIRST-PASS FROZEN
  regular-exit input of planar Brownian motion. No new paper-owned Prop is used.
* `firstPass_3_6_convergence_corrected` proves the same conjunct from the corrected Lemma 3.2.
-/

namespace MatedCRT.FirstPass36

open MatedCRT

/-- The convergence part of corrected Lemma 3.6 ([C13]): pointwise and uniform convergence in probability of the
discrete harmonic extensions with projected exit-cell data to the classical harmonic extension of the continuous
closed-disc datum. Inputs: Draft Lemma 2.11 (`RandomWalkToLBMStmt`), Draft Lemma 2.8 (`CellSizeEstimateStmt`), External
`MepsScalingInput`, the FIRST-PASS FROZEN `FrozenBrownianOutwardExcursionAtExit`, and Draft Lemma 3.2
(`DiscreteHolderContinuityStmt`). The LBM path-functional measurability is proved (`lbmPathFunctionalMeasurableStep_holds`).
RESTS ON THE PRINTED Lemma 3.2, which is FALSE (docs/campaign/CORRECTED-FORMS.md, row 3.2): use
`firstPass_3_6_convergence_corrected`, which takes the corrected form `FrozenDiscreteHolderContinuityCorrected`. -/
theorem firstPass_3_6_convergence {𝒮 : SpaceFillingSLEModel} (h211 : RandomWalkToLBMStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (h32 : DiscreteHolderContinuityStmt 𝒮) : CorrectedHarmonicConvergenceStmt 𝒮 :=
  correctedHarmonicConvergence_of_discreteHolder 𝒮 h211 hm hexc (lbmPathFunctionalMeasurableStep_holds 𝒮) h28 h32

/-- The convergence part of corrected Lemma 3.6 ([C13]), from the corrected Lemma 3.2.
Same statement and inputs as `firstPass_3_6_convergence`, with `h32 : FrozenDiscreteHolderContinuityCorrected 𝒮`, the
CertifiedReferenceModel conjunct, in place of the printed `DiscreteHolderContinuityStmt 𝒮`. The proof is
`correctedHarmonicConvergence_of_discreteHolderCorrected` (`MatedCRT/FirstPass/S3e/HolderGoodEventCorrected.lean`), which differs
from the printed chain only in the destructuring of the Hölder data. -/
theorem firstPass_3_6_convergence_corrected {𝒮 : SpaceFillingSLEModel} (h211 : RandomWalkToLBMStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) : CorrectedHarmonicConvergenceStmt 𝒮 :=
  correctedHarmonicConvergence_of_discreteHolderCorrected 𝒮 h211 hm hexc (lbmPathFunctionalMeasurableStep_holds 𝒮) h28 h32

end MatedCRT.FirstPass36

#print axioms MatedCRT.FirstPass36.firstPass_3_6_convergence
#print axioms MatedCRT.FirstPass36.firstPass_3_6_convergence_corrected
