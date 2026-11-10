import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.HolderGoodEvent
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.SameWalkAssembly
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.PathFunctionalStep
import MatedCRT.FirstPass.Frozen.S3S4

/-!
# First-pass corrected Lemma 3.6 (task fp-S3e-3-6-corrected)

Corrected Lemma 3.6 of `paper/idla_mated_crt-corrected.tex` ([C13], `lemma:convergence-of-harmonic-functions`) is the
Draft conjunction `CorrectedLemma36Stmt 𝒮 = CorrectedHarmonicConvergenceStmt 𝒮 ∧ CorrectedHarmonicSameWalkRateStmt 𝒮`
(`Draft/Section3HarmonicCorrected.lean`). The old `firstPass_3_6` (`FirstPass/S3S4.lean`) concludes the obsolete
`ConvergenceHarmonicFunctionsStmt` and is left unchanged.

* `firstPass_3_6_convergence` proves the first conjunct from Draft statements of other numbered results
  (Lemma 2.8, Lemma 2.11, Lemma 3.2 in its Draft form), the External `MepsScalingInput`, and the FIRST-PASS FROZEN
  regular-exit input of planar Brownian motion. No new paper-owned Prop is used.
* `firstPass_3_6_corrected_of_rate` packages the two conjuncts, with the second one taken from the paper-owned step
  `UniformSameWalkAssemblyStep`. This is a CONDITIONAL packaging, not a closure of corrected Lemma 3.6: that step has no
  Lean provider (see `reports/z10.md`).
-/

namespace MatedCRT.FirstPass36

open MatedCRT

/-- The convergence part of corrected Lemma 3.6 ([C13]): pointwise and uniform convergence in probability of the
discrete harmonic extensions with projected exit-cell data to the classical harmonic extension of the continuous
closed-disc datum. Inputs: Draft Lemma 2.11 (`RandomWalkToLBMStmt`), Draft Lemma 2.8 (`CellSizeEstimateStmt`), External
`MepsScalingInput`, the FIRST-PASS FROZEN `FrozenBrownianOutwardExcursionAtExit`, and Draft Lemma 3.2
(`DiscreteHolderContinuityStmt`). The LBM path-functional measurability is proved (`lbmPathFunctionalMeasurableStep_holds`). -/
theorem firstPass_3_6_convergence {𝒮 : SpaceFillingSLEModel} (h211 : RandomWalkToLBMStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (h32 : DiscreteHolderContinuityStmt 𝒮) : CorrectedHarmonicConvergenceStmt 𝒮 :=
  correctedHarmonicConvergence_of_discreteHolder 𝒮 h211 hm hexc (lbmPathFunctionalMeasurableStep_holds 𝒮) h28 h32

/-- CONDITIONAL, NOT A CLOSURE of corrected Lemma 3.6. The convergence conjunct is proved from the inputs of
`firstPass_3_6_convergence`; the same-walk conjunct `CorrectedHarmonicSameWalkRateStmt 𝒮` is obtained from the
paper-owned step `UniformSameWalkAssemblyStep 𝒮` (`Proofs/Sec3/ConvergenceHarmonicFunctions/SameWalkAssembly.lean`),
which has no Lean provider. The fleet reports the pointwise clause of `CorrectedHarmonicSameWalkRateStmt` as false
(`notes/wpn-steps2/steps2-r2.tex`, lines 491–512); that claim is unresolved for valid environments. -/
theorem firstPass_3_6_corrected_of_rate {𝒮 : SpaceFillingSLEModel} (h211 : RandomWalkToLBMStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (h32 : DiscreteHolderContinuityStmt 𝒮) (hrate : UniformSameWalkAssemblyStep 𝒮) : CorrectedLemma36Stmt 𝒮 :=
  ⟨firstPass_3_6_convergence h211 h28 hm hexc h32, correctedHarmonicSameWalkRate_of_assembly 𝒮 hrate⟩

end MatedCRT.FirstPass36

#print axioms MatedCRT.FirstPass36.firstPass_3_6_convergence
#print axioms MatedCRT.FirstPass36.firstPass_3_6_corrected_of_rate
