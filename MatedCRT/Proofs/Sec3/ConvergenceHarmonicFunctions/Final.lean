import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.HarmonicPathExit
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.WalkMeasurability

/-! # Lemma 3.6: final form of the reduction -/

namespace MatedCRT

/-- The path step of Lemma 3.6 with the walk measurability discharged. -/
theorem harmonicPathExitStep_of_inputs (𝒮 : SpaceFillingSLEModel)
    (hexc : BrownianOutwardExcursionAtExitStep) (hX : LBMPathFunctionalMeasurableStep 𝒮) :
    HarmonicPathExitStep 𝒮 :=
  harmonicPathExitStep_of_steps 𝒮 hexc hX interpolatedWalkMeasurableStep

/-- **Lemma 3.6**, final form: from Theorem 2.11 and Lemma 2.8 (cited), the Brownian
regular-exit input, measurability of LBM path functionals, and the exit-cell
comparison `HarmonicExitCellStep` (whose printed proof has the gap E-c2-8). -/
theorem convergenceHarmonicFunctions_final (𝒮 : SpaceFillingSLEModel)
    (h211 : RandomWalkToLBMStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hexc : BrownianOutwardExcursionAtExitStep) (hX : LBMPathFunctionalMeasurableStep 𝒮)
    (hcell : HarmonicExitCellStep 𝒮) : ConvergenceHarmonicFunctionsStmt 𝒮 :=
  convergenceHarmonicFunctions_of_steps 𝒮 h211 h28 (harmonicPathExitStep_of_inputs 𝒮 hexc hX)
    hcell

end MatedCRT
