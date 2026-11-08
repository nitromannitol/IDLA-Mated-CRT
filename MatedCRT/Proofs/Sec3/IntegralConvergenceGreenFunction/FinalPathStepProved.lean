import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.FinalGreen
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.LBMExitTimeIntegrable
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.PathFunctionalStep

/-!
# Lemma 3.4: the assemblies with the path-functional step proved

`integralConvergenceGreenFunction_of_inputs_green` and `lbmExitTimeIntegrableStep_of_inputs` take the step
`LBMPathFunctionalMeasurableStep 𝒮` as a hypothesis. That step holds for every space-filling model
(`lbmPathFunctionalMeasurableStep_holds`, `PathFunctionalStep.lean`, GAPS-SEC3 item 4), so both are restated without it.
The hypotheses that remain are the Section 3 inputs and steps still open: `hrevuz` (`LBMGreenOccupationStep`, owned by m1/y5),
`hfixedStep` (`TruncatedOccupationFixedTimeStep`, which needs the deterministic input H1 still open), `hmeasStep`
(`LBMTruncatedOccupationMeasurableStep`, open: the environment-dependent extension of the path-functional step), and `hexc`
(`BrownianOutwardExcursionAtExitStep`, no Lean statement yet).
-/

namespace MatedCRT

/-- **Lemma 3.4 from the named Section 3 inputs, with the path-functional step proved.** -/
theorem integralConvergenceGreenFunction_of_inputs_pathStepProved {𝒮 : SpaceFillingSLEModel}
    (h17 : BoundedExitTimeRVStmt) (h18 : ExitTimeUpperBoundStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    (hrevuz : LBMGreenOccupationStep 𝒮) (hfixedStep : TruncatedOccupationFixedTimeStep 𝒮)
    (h211 : RandomWalkToLBMStmt 𝒮) (hcell : CellSizeEstimateStmt 𝒮)
    (hexc : BrownianOutwardExcursionAtExitStep) (hmeasStep : LBMTruncatedOccupationMeasurableStep 𝒮) :
    IntegralConvergenceGreenFunctionStmt 𝒮 :=
  integralConvergenceGreenFunction_of_inputs_green h17 h18 hscale hrevuz hfixedStep h211
    (lbmPathFunctionalMeasurableStep_holds 𝒮) hcell hexc hmeasStep

/-- **The exit-time integrability step, with the path-functional step proved.** -/
theorem lbmExitTimeIntegrableStep_holds_of_inputs {𝒮 : SpaceFillingSLEModel}
    (h17 : BoundedExitTimeRVStmt) (h18 : ExitTimeUpperBoundStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    (h211 : RandomWalkToLBMStmt 𝒮) (hcell : CellSizeEstimateStmt 𝒮)
    (hexc : BrownianOutwardExcursionAtExitStep) : LBMExitTimeIntegrableStep 𝒮 :=
  lbmExitTimeIntegrableStep_of_inputs h17 h18 hscale h211 (lbmPathFunctionalMeasurableStep_holds 𝒮) hcell hexc

end MatedCRT
