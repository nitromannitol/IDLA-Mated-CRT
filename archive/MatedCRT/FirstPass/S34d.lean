import MatedCRT.FirstPass.S3S4c
import MatedCRT.FirstPass.Frozen.S3S4
import MatedCRT.FirstPass.S3t
import MatedCRT.FirstPass.S3t.BLEnvelopeClosure

/-!
# Lemma 3.4 with the truncated quenched laws derived

`firstPass_3_4_derived` is `MatedCRT.S3S4c.firstPass_3_4` (`FirstPass/S3S4c.lean:149`) without the frozen hypothesis
`hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮`. `firstPass_3_4_derived` takes the local hypothesis `hT`, standing
for the derivation `truncatedQuenchedLawsFixedTime_of_inputs`.

`firstPass_3_4_derived_closed` takes no `hT`: it uses the four-binder theorem
`MatedCRT.TruncatedLaws.truncatedQuenchedLawsFixedTime_of_inputs` (`FirstPass/S3t/BLEnvelopeClosure.lean:43`, commit
4c8c580), whose only inputs are `h211 h28 hm hexc`. The Brownian measurability facts that the staged form took as the
binders `hmeas`, `hShellMeas` are supplied by the named closure input `BLEnvelopeClosureInput` inside that theorem
(`blEnvelopeClosureInput_holds`, `FirstPass/S3t/BLEnvelopeClosure.lean:29`). Terminology: Berestycki–Powell,
Armitage–Gardiner for the Green function; Duplantier–Sheffield for the LQG measure.
-/

namespace MatedCRT

/-- **Lemma 3.4 (integral convergence of the Green function), truncated quenched laws derived.** Same conclusion as
`MatedCRT.S3S4c.firstPass_3_4`; the frozen input `hdet` is replaced by `hT` applied to `h211`, `h28`, `hm`, `hexc`. -/
theorem firstPass_3_4_derived {𝒮 : SpaceFillingSLEModel} (h27 : VolumeGrowthStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hm : MepsScalingInput 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h211 : RandomWalkToLBMStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hT : RandomWalkToLBMStmt 𝒮 → CellSizeEstimateStmt 𝒮 → MepsScalingInput 𝒮 →
      BrownianOutwardExcursionAtExitStep → FrozenTruncatedQuenchedLawsFixedTime 𝒮) :
    IntegralConvergenceGreenFunctionStmt 𝒮 :=
  S3S4c.firstPass_3_4 h27 h218 hm hrevuz (hT h211 h28 hm hexc)

#print axioms firstPass_3_4_derived

/-- **Lemma 3.4 (integral convergence of the Green function), truncated quenched laws derived from the four-binder
theorem.** Same conclusion as `MatedCRT.S3S4c.firstPass_3_4`. The frozen input `hdet` is replaced by
`MatedCRT.TruncatedLaws.truncatedQuenchedLawsFixedTime_of_inputs` (`FirstPass/S3t/BLEnvelopeClosure.lean:43`) applied to
`h211`, `h28`, `hm`, `hexc`. No measurability binder remains. -/
theorem firstPass_3_4_derived_closed {𝒮 : SpaceFillingSLEModel} (h27 : VolumeGrowthStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hm : MepsScalingInput 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h211 : RandomWalkToLBMStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hexc : FrozenBrownianOutwardExcursionAtExit) :
    IntegralConvergenceGreenFunctionStmt 𝒮 :=
  S3S4c.firstPass_3_4 h27 h218 hm hrevuz
    (MatedCRT.TruncatedLaws.truncatedQuenchedLawsFixedTime_of_inputs h211 h28 hm hexc)

#print axioms firstPass_3_4_derived_closed

end MatedCRT
