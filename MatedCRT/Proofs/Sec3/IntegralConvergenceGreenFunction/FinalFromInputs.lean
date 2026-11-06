import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.Final
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.LBMExitTimeIntegrable

/-!
# Lemma 3.4: assembly from the named Section 3 inputs

`integralConvergenceGreenFunction_of_inputs` is `integralConvergenceGreenFunction_of_steps` with its step
`hexitStep : LBMExitTimeIntegrableStep 𝒮` discharged by `lbmExitTimeIntegrableStep_of_inputs`. The assembly
therefore takes the named inputs of that proof (the bounded exit-time and exit-time-tail statements,
`MepsScalingInput`, the walk convergence `RandomWalkToLBMStmt`, `LBMPathFunctionalMeasurableStep`,
`CellSizeEstimateStmt` and `BrownianOutwardExcursionAtExitStep`) in place of `hexitStep`. The old theorem and its
statement are unchanged. This file sits above `LBMExitTimeIntegrable`, which imports `Final`.
-/

namespace MatedCRT

/-- **Lemma 3.4** from the named Section 3 inputs: the rescaled Green occupation sums converge in probability to
`c₀ ∫ G f dμ_h`, given the Revuz identity, the fixed-time and measurability steps, and the named inputs of
`lbmExitTimeIntegrableStep_of_inputs` for the integrability of the LBM exit time. -/
theorem integralConvergenceGreenFunction_of_inputs {𝒮 : SpaceFillingSLEModel}
    (h17 : BoundedExitTimeRVStmt) (h18 : ExitTimeUpperBoundStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    (hrevuz : LBMGreenOccupationStep 𝒮) (hfixedStep : TruncatedOccupationFixedTimeStep 𝒮)
    (h211 : RandomWalkToLBMStmt 𝒮) (hX : LBMPathFunctionalMeasurableStep 𝒮) (hcell : CellSizeEstimateStmt 𝒮)
    (hexc : BrownianOutwardExcursionAtExitStep) (hmeasStep : LBMTruncatedOccupationMeasurableStep 𝒮)
    (hUmStep : LBMGreenIntegralMeasurableStep 𝒮) :
    IntegralConvergenceGreenFunctionStmt 𝒮 :=
  integralConvergenceGreenFunction_of_steps h17 h18 hscale hrevuz hfixedStep
    (lbmExitTimeIntegrableStep_of_inputs h17 h18 hscale h211 hX hcell hexc) hmeasStep hUmStep

end MatedCRT
