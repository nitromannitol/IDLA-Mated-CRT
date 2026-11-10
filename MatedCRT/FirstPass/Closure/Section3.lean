import MatedCRT.FirstPass.S3S4
import MatedCRT.FirstPass.S3S4c

/-!
# Closed results, Section 3 (task fp-Closure-counted-results, worker z1)

Closed: 3.1 (`closed_3_1`, S3S4 corrected form), 3.3 (`closed_3_3`), 3.4 (`closed_3_4`, module `S3S4c`),
3.6 (`closed_3_6`). Not closed: 3.5 (needs `CorrectedHarmonicConvergenceStmt`, no firstPass provider), 3.7
(needs the printed Lemma 3.5 `DiscreteDirichletProblemStmt`, which is not provided). See the report.
-/

namespace MatedCRT

/-- Lemma 3.1 (discrete potential tightness), closed in the corrected form. Conclusion
`DiscretePotentialTightnessCorrectedStmt 𝒮`. -/
alias closed_3_1 := firstPass_3_1_corrected

/-- Lemma 3.4 (integral convergence of the Green function), closed. Hypotheses: `VolumeGrowthStmt`,
`ExitTimeUpperBoundStmt 𝒮` (cited), `MepsScalingInput 𝒮` (External), and two frozen Props. -/
alias closed_3_4 := MatedCRT.S3S4c.firstPass_3_4

/-- Lemma 3.3 (uniform convergence of the Green kernel), closed. The paper-owned input
`IntegralConvergenceGreenFunctionStmt 𝒮` (Lemma 3.4) is discharged by `closed_3_4`. -/
theorem closed_3_3 {𝒮 : SpaceFillingSLEModel} (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮) (h27 : VolumeGrowthStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hm : MepsScalingInput 𝒮)
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮) : UniformConvergenceGreenKernelStmt 𝒮 :=
  firstPass_3_3 (h34 := closed_3_4 h27 h218 hm hrevuz hdet) h210 h214 h28 h27 h218 hm h32

/-- Lemma 3.6 (convergence of harmonic functions), closed. -/
alias closed_3_6 := firstPass_3_6

end MatedCRT
