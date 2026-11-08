import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.FinalFromInputs
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.GreenIntegralMeasurable

/-!
# Lemma 3.4: assembly with the Green-integral measurability proved

`integralConvergenceGreenFunction_of_steps_green` is `integralConvergenceGreenFunction_of_steps` with its step
`hUmStep : LBMGreenIntegralMeasurableStep 𝒮` discharged by `lbmGreenIntegralMeasurableStep_holds`.
`integralConvergenceGreenFunction_of_inputs_green` is `integralConvergenceGreenFunction_of_inputs` with the same
step discharged; its named inputs are those of `lbmExitTimeIntegrableStep_of_inputs`.

Hypotheses of Lemma 3.4 that remain after this file, besides the cited Draft and External statements
(`BoundedExitTimeRVStmt`, `ExitTimeUpperBoundStmt`, `MepsScalingInput`, `RandomWalkToLBMStmt`, `CellSizeEstimateStmt`):
* `LBMGreenOccupationStep 𝒮` (the Revuz identity, IR-m2-1, awaiting the operator);
* `TruncatedOccupationFixedTimeStep 𝒮` (fixed-time convergence for environment-dependent test functions, E-c2-9);
* `LBMTruncatedOccupationMeasurableStep 𝒮` (measurability of the truncated occupations);
* in the `_of_inputs_green` form also `LBMPathFunctionalMeasurableStep 𝒮` and `BrownianOutwardExcursionAtExitStep`.
-/

namespace MatedCRT

/-- **Lemma 3.4** from its steps, with the measurability of the Green integral proved: the rescaled Green
occupation sums converge in probability to `c₀ ∫ G f dμ_h`, given the Revuz identity `LBMGreenOccupationStep`, the
fixed-time and truncated-measurability steps, and the exit-time integrability step. -/
theorem integralConvergenceGreenFunction_of_steps_green {𝒮 : SpaceFillingSLEModel}
    (h17 : BoundedExitTimeRVStmt) (h18 : ExitTimeUpperBoundStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    (hrevuz : LBMGreenOccupationStep 𝒮) (hfixedStep : TruncatedOccupationFixedTimeStep 𝒮)
    (hexitStep : LBMExitTimeIntegrableStep 𝒮) (hmeasStep : LBMTruncatedOccupationMeasurableStep 𝒮) :
    IntegralConvergenceGreenFunctionStmt 𝒮 :=
  integralConvergenceGreenFunction_of_steps h17 h18 hscale hrevuz hfixedStep hexitStep hmeasStep
    (lbmGreenIntegralMeasurableStep_holds 𝒮)

/-- **Lemma 3.4** from the named Section 3 inputs, with the measurability of the Green integral proved. -/
theorem integralConvergenceGreenFunction_of_inputs_green {𝒮 : SpaceFillingSLEModel}
    (h17 : BoundedExitTimeRVStmt) (h18 : ExitTimeUpperBoundStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    (hrevuz : LBMGreenOccupationStep 𝒮) (hfixedStep : TruncatedOccupationFixedTimeStep 𝒮)
    (h211 : RandomWalkToLBMStmt 𝒮) (hX : LBMPathFunctionalMeasurableStep 𝒮) (hcell : CellSizeEstimateStmt 𝒮)
    (hexc : BrownianOutwardExcursionAtExitStep) (hmeasStep : LBMTruncatedOccupationMeasurableStep 𝒮) :
    IntegralConvergenceGreenFunctionStmt 𝒮 :=
  integralConvergenceGreenFunction_of_inputs h17 h18 hscale hrevuz hfixedStep h211 hX hcell hexc hmeasStep
    (lbmGreenIntegralMeasurableStep_holds 𝒮)

end MatedCRT
