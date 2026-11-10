import MatedCRT.FirstPass.S3S4c
import MatedCRT.FirstPass.Frozen.S3S4

/-!
# Lemma 3.4 with the truncated quenched laws derived (fp-S3t-consumers, z5)

`firstPass_3_4_derived` is `MatedCRT.S3S4c.firstPass_3_4` (`FirstPass/S3S4c.lean:149`) with the frozen hypothesis
`hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮` removed. The input is the local hypothesis `hT`, which stands for the
derivation `truncatedQuenchedLawsFixedTime_of_inputs` (z8, `FirstPass/S3t.lean`, not yet committed) with arguments
`h211`, `h28`, `hm`, `hexc` (note `notes/fp-gaps/CHATGPT-idla-3-4-truncated-laws.md` §4). When z8 commits that theorem,
replace `hT` by it. The old `firstPass_3_4` is unchanged. Terminology: Berestycki–Powell, Armitage–Gardiner for the
Green function; Duplantier–Sheffield for the LQG measure.
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

end MatedCRT
