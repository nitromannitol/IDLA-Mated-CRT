import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.TruncatedStepsProved
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.FinalPathStepProved

/-!
# Lemma 3.4 (lemma:integral-convergence-of-greens-function): the final assembly

`integralConvergenceGreenFunction_final` derives `IntegralConvergenceGreenFunctionStmt 𝒮` from the inputs that remain
open, stated as explicit hypotheses:
* `hscale`, `h17`, `h18`, `h211`, `hcell`: the cited scaling, exit-time and random-walk inputs of the Draft (as in
  `integralConvergenceGreenFunction_of_inputs_pathStepProved`);
* `hrevuz`: the Revuz identity `LBMGreenOccupationStep` (IR-m2-1, pending with the operator);
* `hdet`: the deterministic fixed-time step `TruncatedDetFixedTimeStep` (D1, route PROOF-REPAIRS-G §G4; open);
* `hexc`: `BrownianOutwardExcursionAtExitStep` (queued for a worker; carried as a hypothesis).

Proved in this directory and used here: the environment-dependent truncated path integrals are measurable
(`lbmTruncatedOccupationMeasurableStep_holds`, item 3) and their fixed-time integrability
(`truncatedFixedTimeIntegrableStep_holds`, item 2-H2); the Green integral measurability and the path-functional steps
are proved as in the assembly.
-/

namespace MatedCRT

/-- **Lemma 3.4 from its remaining inputs.** -/
theorem integralConvergenceGreenFunction_final {𝒮 : SpaceFillingSLEModel}
    (h17 : BoundedExitTimeRVStmt) (h18 : ExitTimeUpperBoundStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    (hrevuz : LBMGreenOccupationStep 𝒮) (hdet : TruncatedDetFixedTimeStep 𝒮)
    (h211 : RandomWalkToLBMStmt 𝒮) (hcell : CellSizeEstimateStmt 𝒮)
    (hexc : BrownianOutwardExcursionAtExitStep) :
    IntegralConvergenceGreenFunctionStmt 𝒮 :=
  integralConvergenceGreenFunction_of_inputs_pathStepProved h17 h18 hscale hrevuz
    (truncatedOccupationFixedTimeStep_of_det hscale hdet (truncatedFixedTimeIntegrableStep_holds 𝒮))
    h211 hcell hexc (lbmTruncatedOccupationMeasurableStep_holds 𝒮)

end MatedCRT
