import MatedCRT.Proofs.Sec4.ConvergenceDivisible.CorrectedInputs
import MatedCRT.Proofs.Sec4.SubsequentialProperties.Final
import MatedCRT.Steps.Sec2.MaximumPrinciple

/-!
# Theorem 4.1: final form

`convergenceDivisible_final` proves `ConvergenceDivisibleStmt` from m4's corrected route
(`convergenceDivisible_of_corrected_reductions`, CorrectedInputs.lean) with the corrected distributional limit step of
Lemma 4.8 proved (`odometerDistributionalLimitCorrectedStep_of_greenKernel`, from Lemma 3.3) and Lemma 2.13 proved.

Remaining hypotheses: Lemmas 2.7, 2.18 (cited), `MepsScalingInput` (External); Lemmas 3.3, 3.5, 3.7 (Draft, reduced
elsewhere); the open steps `ConeEnvironmentScalingStep` (m1), `DiscreteHolderContinuityCorrectedStep` (corrected
Lemma 3.1), `OdometerLocalCompactnessCorrectedStep`, `OdometerBoundaryUpgradeCorrectedStep`,
`OdometerMeasurableSelectionStep` (Lemma 4.6; E-x3-2).
-/

namespace MatedCRT

/-- **Theorem 4.1** from the hypotheses listed in the module docstring. -/
theorem convergenceDivisible_final (𝒮 : SpaceFillingSLEModel)
    -- cited / External
    (h27 : VolumeGrowthStmt) (h218 : ExitTimeUpperBoundStmt 𝒮) (hm : MepsScalingInput 𝒮)
    -- earlier results (reduced elsewhere)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h37 : ConvergenceNormalizedExitTimeStmt 𝒮)
    -- open steps
    (hscale : ConeEnvironmentScalingStep 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (hlocal : OdometerLocalCompactnessCorrectedStep 𝒮) (hboundary : OdometerBoundaryUpgradeCorrectedStep 𝒮)
    (hselect : OdometerMeasurableSelectionStep 𝒮) : ConvergenceDivisibleStmt 𝒮 :=
  convergenceDivisible_of_corrected_reductions 𝒮 h27 hscale hm h218 hH h33 h35 h37
    (maximumPrinciple_of_steps (adjacentCellsMeetAeStep 𝒮)) hlocal hboundary hselect
    (odometerDistributionalLimitCorrectedStep_of_greenKernel 𝒮 h33)

end MatedCRT
