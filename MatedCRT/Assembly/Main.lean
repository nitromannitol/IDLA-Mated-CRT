import MatedCRT.Assembly.Hypotheses
import MatedCRT.Proofs.Sec1.Main
import MatedCRT.Proofs.Sec1.ConeScaleRadius
import MatedCRT.Steps.Sec8.IDLAConstrainedConvergence
import MatedCRT.Proofs.Measurability.ConeScaleInputs
import MatedCRT.Steps.Sec2.MaximumPrinciple
import MatedCRT.Steps.Sec2.BoundedExitTimeRV
import MatedCRT.Steps.Sec2.ExpectedExitTimeExplicitBound
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Final
import MatedCRT.Steps.Sec3.ConvergenceHarmonicFunctions
import MatedCRT.Steps.Sec3.UniformConvergenceGreenKernel
import MatedCRT.Steps.Sec3.DiscreteDirichletProblem
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.OfInteriorBoundary
import MatedCRT.Proofs.Sec4.ObstacleSpecialization.Final
import MatedCRT.Proofs.Sec4.Equibounded
import MatedCRT.Proofs.Sec4.SubsequentialConvergence.Corrected
import MatedCRT.Proofs.Sec4.SubsequentialProperties.Corrected
import MatedCRT.Proofs.Sec4.SubsequentialProperties.ObstacleApproximation
import MatedCRT.Steps.Sec4.ConvergenceDivisible
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.MaximumPrinciple
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.LocalExitReduction
import MatedCRT.Proofs.Measurability.ConvergenceDivisibleEvent
import MatedCRT.Steps.Sec4.DivSandpileLowerBound
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.OdometerComparison
import MatedCRT.Steps.Sec5.MeanValueInequality
import MatedCRT.Steps.Sec5.IDLALowerBound
import MatedCRT.Proofs.Sec5.LLowerBound.OfEvents
import MatedCRT.Proofs.Sec5.MeanValueInequality.NormalizedStep
import MatedCRT.Proofs.Sec5.MeanValueInequality.SurplusSteps
import MatedCRT.Proofs.Measurability.EnvSigma
import MatedCRT.Proofs.Sec6.AnnulusHit.Main
import MatedCRT.Proofs.Sec6.GoodAnnulusPrevalence.Main
import MatedCRT.Proofs.Field.LawTransferComplete
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Final
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.LogLoss
import MatedCRT.Proofs.Sec6.ChanceOfBeingAbsorbed.Chernoff
import MatedCRT.Proofs.Sec6.ChanceOfBeingAbsorbed.LogLoss
import MatedCRT.Proofs.Sec6.IterativeBound.Statement
import MatedCRT.Proofs.Sec6.IDLAUpperBound.OfSteps
import MatedCRT.Proofs.Measurability.BoundaryLayer
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ComponentReduction
import MatedCRT.Proofs.Sec7.OdometerBoundMass.Corrected
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ShellIterationOfMeshScaling
import MatedCRT.Proofs.Sec2.Final
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.DyadicModulus
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.Final
import MatedCRT.Proofs.Sec5.IDLALowerBound.Final
import MatedCRT.Proofs.Measurability.LQGMeasureField
import MatedCRT.Proofs.Field.ConeCircleModConst
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.InteriorStep
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ExitCell
import MatedCRT.Proofs.Sec4.SubsequentialProperties.Final
import MatedCRT.Proofs.Sec5.StoppedFinal
import MatedCRT.Proofs.Sec5.StoppedLLowerBound
import MatedCRT.Proofs.Sec4.Prop42Closure.Assembly
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.Limit

/-!
# Theorems 1.4 and 1.6, conditional on the remaining hypotheses

`convergenceOfIDLA_conditional` and `convergenceOfDivSandpile_conditional` compose, by application only, the committed
reductions of the numbered results of "Internal DLA on mated-CRT maps" (arXiv:2211.04891) into Theorems 1.4 and 1.6,
under `MainHypotheses 𝒮` (MatedCRT/Assembly/Hypotheses.lean). Each numbered result on the way is one theorem
`MainHypotheses.<result>` below, proved by its reduction applied to the earlier results, to fields of `MainHypotheses`
and to proved steps; MatedCRT/Audit/Main.lean checks that every reduction is indeed used, and that no field of
`MainHypotheses` is a Draft statement refuted in Lean.

The main line: Theorems 1.4, 1.6 ← Proposition 8.1 (`iDLAConstrainedConvergence_of_steps`) ← Propositions 4.2, 5.1,
6.1, 7.1, with the scaling argument of Section 8.1 (`convergenceOfIDLA_of_coneSteps`). Proved results and steps
discharged here: Lemmas 2.13, 4.3, 4.4 (corrected), 7.3 (from 4.4 corrected), 6.6 (inside 6.4),
`adjacentCellsMeetAeStep`, `obstacleLimitUniqueness`, `odometerObstacleApproximationStep`,
`coneScaleRadiusPosStep_of_input`, `Absorption.absorptionChernoffStep`, `LQGMeasureField.lqgMeasureFieldMeasurableStep`,
`Field.ConeCircle.circleAverageModConstStep`, the two steps of Lemma 3.3 (`uniformConvergenceGreenKernel_final`),
`HarmonicPathExitStep` and `HarmonicExitCellStep` of Lemma 3.6 (`convergenceHarmonicFunctions_of_inputs`),
`OdometerDistributionalLimitCorrectedStep` of Lemma 4.8 (`subsequentialProperties_of_inputs`),
`StoppedLLowerBoundStep` (`stoppedLLowerBound_of_inputs`); `StoppedMeanValueInequalityStep` is reduced to three
obstacle-surplus steps (`stoppedMeanValueInequality_of_steps`).

Corrected forms used where the Draft is false or open: 3.1 corrected (by 3.5, 4.6), 3.1 almost-sure corrected (E-c2-6,
by 3.3, 3.7), 4.4 corrected (by 5.1, 5.3, 7.2-7.4), the E-A10 (b) log-loss forms of 6.7, 6.8, 6.9 (by 6.10, 7.1),
7.2 corrected (above scale, by 7.1). No Draft form reported false is consumed: the Draft 3.1, refuted in Lean
(Audit/Refutations.lean), is not a field of `MainHypotheses` any more.

This file is regenerated as steps close; keep it mechanical.
-/

namespace MatedCRT

namespace MainHypotheses

variable {𝒮 : SpaceFillingSLEModel}

/-! ## Section 2 -/

/-- **Lemma 2.4** (`coneHarmonicBallsUpToFixedTime_final`: the whole-plane harmonic balls from the [BG22] Drafts). -/
theorem coneHarmonicBallsUpToFixedTime (H : MainHypotheses 𝒮) : ConeHarmonicBallsUpToFixedTimeStmt :=
  coneHarmonicBallsUpToFixedTime_final H.harmonicBallsDraftInputs H.wholePlaneLogLQGExistence H.coneRestriction
    H.coneHarmonicBallLocality H.coneHarmonicBallStrictGrowth

/-- **Lemma 2.5** (`coneScaleInvarianceUpToFixedTime_of_scaleRadiusPos`, with `coneScaleRadiusPosStep_of_input`). -/
theorem coneScaleInvarianceUpToFixedTime (H : MainHypotheses 𝒮) : ConeScaleInvarianceUpToFixedTimeStmt :=
  coneScaleInvarianceUpToFixedTime_of_scaleRadiusPos H.quantumConeScaling H.lqgMeasureProperties
    (coneScaleRadiusPosStep_of_input H.quantumConeScaling) H.coneHarmonicBallStrictGrowth H.coneHalfBallFamilyFunctional

/-- The families of Lemmas 2.4, 2.5 are random variables (`coneFamilyAEMeasurableStep_of_inputs`). -/
theorem coneFamilyAEMeasurable (H : MainHypotheses 𝒮) : ConeFamilyAEMeasurableStep :=
  coneFamilyAEMeasurableStep_of_inputs H.quantumConeScaling H.coneHarmonicBallStrictGrowth H.lqgMeasureProperties
    (coneScaleRadiusPosStep_of_input H.quantumConeScaling) H.coneHalfBallFamilyFunctional

/-- **Theorem 2.3** (`coneHarmonicBalls_of_steps`). -/
theorem coneHarmonicBalls (H : MainHypotheses 𝒮) : ConeHarmonicBallsStmt :=
  coneHarmonicBalls_of_steps H.coneHarmonicBallsUpToFixedTime H.coneScaleInvarianceUpToFixedTime
    H.coneFamilyAEMeasurable

/-- **Lemma 2.13** (`maximumPrinciple_of_steps`, with `adjacentCellsMeetAeStep`). -/
theorem maximumPrinciple (𝒮 : SpaceFillingSLEModel) : MaximumPrincipleStmt 𝒮 :=
  maximumPrinciple_of_steps (adjacentCellsMeetAeStep 𝒮)

/-- **Lemma 2.17** (`boundedExitTimeRV_of_steps`). -/
theorem boundedExitTimeRV (H : MainHypotheses 𝒮) : BoundedExitTimeRVStmt :=
  boundedExitTimeRV_of_steps H.volumeGrowth

/-- **Lemma 2.19** (`expectedExitTimeExplicitBound_of_steps`). -/
theorem expectedExitTimeExplicitBound (H : MainHypotheses 𝒮) : ExpectedExitTimeExplicitBoundStmt 𝒮 :=
  expectedExitTimeExplicitBound_of_steps H.boundedExitTimeRV H.exitTimeUpperBound

/-! ## Section 3 -/

/-- **Lemma 3.1**, corrected form (`discretePotentialTightnessCorrected_of_inputs`). -/
theorem discretePotentialTightnessCorrected (H : MainHypotheses 𝒮) : DiscretePotentialTightnessCorrectedStmt 𝒮 :=
  discretePotentialTightnessCorrected_of_inputs H.mepsScaling H.volumeGrowth H.exitTimeUpperBound
    H.discreteHolderContinuityCorrected

/-- **Lemma 3.6** (`convergenceHarmonicFunctions_of_inputs`, ab6ed20: Theorem 2.11, Lemma 2.8, `MepsScalingInput`
and two steps). -/
theorem convergenceHarmonicFunctions (H : MainHypotheses 𝒮) : ConvergenceHarmonicFunctionsStmt 𝒮 :=
  convergenceHarmonicFunctions_of_inputs 𝒮 H.randomWalkToLBM H.cellSizeEstimate H.mepsScaling
    H.brownianOutwardExcursionAtExit H.lbmPathFunctionalMeasurable

/-- **Lemma 3.3** (`uniformConvergenceGreenKernel_final`, 763b7d7: through the almost-sure corrected Lemma 3.1, its
interior and boundary steps proved; no Draft 3.1). -/
theorem uniformConvergenceGreenKernel (H : MainHypotheses 𝒮) : UniformConvergenceGreenKernelStmt 𝒮 :=
  uniformConvergenceGreenKernel_final 𝒮 H.degreeMeasureConvergence H.integralConvergenceGreenFunction
    H.greenKernelUpperBound H.cellSizeEstimate H.discretePotentialTightnessAe

/-- **Lemma 3.5** (`discreteDirichletProblem_of_steps`; `DirichletLimitStep` from `volumeGrowth` by
`dirichletLimitStep_of_volumeGrowth`, Proofs/Sec3/DiscreteDirichletProblem/Limit.lean). -/
theorem discreteDirichletProblem (H : MainHypotheses 𝒮) : DiscreteDirichletProblemStmt 𝒮 :=
  discreteDirichletProblem_of_steps 𝒮 H.greenPotentialHolder H.convergenceHarmonicFunctions
    H.integralConvergenceGreenFunction H.discretePotentialTightnessCorrected (maximumPrinciple 𝒮)
    H.expectedExitTimeExplicitBound H.cellSizeEstimate (dirichletLimitStep_of_volumeGrowth 𝒮 H.volumeGrowth)
    H.dirichletInterior H.dirichletBoundary

/-- **Lemma 3.7** (`convergenceNormalizedExitTime_of_statements`, x1, 980cf27: through the almost-sure corrected
Lemma 3.1, E-c2-6; no Draft 3.1). -/
theorem convergenceNormalizedExitTime (H : MainHypotheses 𝒮) : ConvergenceNormalizedExitTimeStmt 𝒮 :=
  convergenceNormalizedExitTime_of_statements 𝒮 H.uniformConvergenceGreenKernel H.discreteDirichletProblem
    H.boundedExitTimeRV H.exitTimeUpperBound H.discretePotentialTightnessAe

/-! ## Section 4 -/

/-- **Lemma 4.7** (`equibounded_of_steps`, with Lemma 4.3 proved: `discreteBasicProperties`). -/
theorem equibounded (H : MainHypotheses 𝒮) : EquiboundedStmt 𝒮 :=
  equibounded_of_steps (discreteBasicProperties 𝒮) H.boundedExitTimeRV H.exitTimeUpperBound H.mepsScaling

/-- **Lemma 4.6** (`subsequentialConvergence_of_corrected`: through the corrected Lemma 3.1, no Lemma 4.4). -/
theorem subsequentialConvergence (H : MainHypotheses 𝒮) : SubsequentialConvergenceStmt 𝒮 :=
  subsequentialConvergence_of_corrected 𝒮 H.equibounded H.discretePotentialTightnessCorrected
    H.discreteDirichletProblem H.odometerLocalCompactnessCorrected H.odometerBoundaryUpgradeCorrected
    H.odometerMeasurableSelection

/-- **Lemma 4.8** (`subsequentialProperties_of_inputs`, 7582c60: no step; `OdometerDistributionalLimitCorrectedStep`
proved from Lemma 3.3). -/
theorem subsequentialProperties (H : MainHypotheses 𝒮) : SubsequentialPropertiesStmt 𝒮 :=
  subsequentialProperties_of_inputs 𝒮 H.uniformConvergenceGreenKernel H.discreteDirichletProblem
    H.convergenceNormalizedExitTime (maximumPrinciple 𝒮)

/-- Theorem 4.1: the convergence event is measurable
(`convergenceDivisibleEventMeasurableStep_of_coneFamilyAEMeasurable`). -/
theorem convergenceDivisibleEventMeasurable (H : MainHypotheses 𝒮) : ConvergenceDivisibleEventMeasurableStep 𝒮 := by
  have h27 := H.volumeGrowth
  have hfam := H.coneFamilyAEMeasurable
  have h24 := H.coneHarmonicBallsUpToFixedTime
  apply convergenceDivisibleEventMeasurableStep_of_coneFamilyAEMeasurable <;> assumption

/-- **Theorem 4.1** (`convergenceDivisible_of_steps`, with `obstacleLimitUniqueness`). -/
theorem convergenceDivisible (H : MainHypotheses 𝒮) : ConvergenceDivisibleStmt 𝒮 :=
  convergenceDivisible_of_steps 𝒮 H.subsequentialProperties H.subsequentialConvergence
    (obstacleLimitUniqueness 𝒮) H.convergenceDivisibleEventMeasurable

/-- **Proposition 4.2** (`divSandpileLowerBound_prop42`, Proofs/Sec4/Prop42Closure/Assembly.lean, the printed form of
`divSandpileLowerBound_final`, x3, fb05dfd: the inner approximation from the strict obstacle gap). -/
theorem divSandpileLowerBound (H : MainHypotheses 𝒮) : DivSandpileLowerBoundStmt 𝒮 :=
  divSandpileLowerBound_prop42 𝒮 H.convergenceDivisible H.coneHarmonicBalls H.coneHarmonicBallsUpToFixedTime
    H.volumeGrowth H.cellSizeEstimate H.uniformConvergenceGreenKernel H.coneFamilyAEMeasurable
    H.harmonicBallStrictObstacleGap

/-! ## Section 5 -/

/-- Lemma 5.3: the surplus step (`meanValueSurplusStep_of_lower`). -/
theorem meanValueSurplus (H : MainHypotheses 𝒮) : MeanValueSurplusStep 𝒮 :=
  meanValueSurplusStep_of_lower H.boundedExitTimeRV (LQGMeasureField.lqgMeasureFieldMeasurableStep 𝒮)
    H.meanValueSurplusLower

/-- **Lemma 5.3** (`meanValueInequality_of_surplus`, on Lemma 4.4 corrected, proved). -/
theorem meanValueInequality (H : MainHypotheses 𝒮) : MeanValueInequalityStmt 𝒮 := by
  have h44 := discreteLaplacianBoundCorrected 𝒮
  have h213 := maximumPrinciple 𝒮
  have h41 := H.convergenceDivisible
  have h33 := H.uniformConvergenceGreenKernel
  have h218 := H.exitTimeUpperBound
  have hsur := H.meanValueSurplus
  apply meanValueInequality_of_surplus <;> assumption

/-- **Lemma 5.4** (`lLowerBound_of_adjacentCellsMeet`). -/
theorem lLowerBound (H : MainHypotheses 𝒮) : LLowerBoundStmt 𝒮 := by
  have h215 := H.greenFunctionCrudeBound
  have h216 := H.greenKernelLowerBound
  have h29 := H.countingMeasureConvergence
  have hcell := adjacentCellsMeetAeStep 𝒮
  apply lLowerBound_of_adjacentCellsMeet <;> assumption

/-- The discrete-cluster form of Proposition 4.2 used by Proposition 5.1 (`discreteClusterInnerBound_prop42`,
Proofs/Sec4/Prop42Closure/Assembly.lean). -/
theorem discreteClusterInnerBound (H : MainHypotheses 𝒮) : DiscreteClusterInnerBoundStep 𝒮 :=
  discreteClusterInnerBound_prop42 𝒮 H.convergenceDivisible H.coneHarmonicBalls H.coneHarmonicBallsUpToFixedTime
    H.volumeGrowth H.cellSizeEstimate H.uniformConvergenceGreenKernel H.coneFamilyAEMeasurable
    H.harmonicBallStrictObstacleGap

/-- Lemma 5.3 on `V^ε(Λ_t)` (E-c1-5; `stoppedMeanValueInequality_of_steps`, 16ca787: three obstacle-surplus steps). -/
theorem stoppedMeanValueInequality (H : MainHypotheses 𝒮) : StoppedMeanValueInequalityStep 𝒮 :=
  stoppedMeanValueInequality_of_steps 𝒮 H.convergenceDivisible H.uniformConvergenceGreenKernel H.exitTimeUpperBound
    H.integralConvergenceGreenFunction H.boundedExitTimeRV H.stoppedSurplusInterior
    (stoppedSurplusExterior_of_nullMeasurableOrigin 𝒮 H.mepsScaling H.coneOriginNullMeasurable)
    H.stoppedLayerPotential

/-- Lemma 5.4 on `V^ε(Λ_t)` (E-c1-5; `stoppedLLowerBound_of_inputs`, a9952ca: from Lemmas 2.9, 2.15, 2.16). -/
theorem stoppedLLowerBound (H : MainHypotheses 𝒮) : StoppedLLowerBoundStep 𝒮 :=
  stoppedLLowerBound_of_inputs 𝒮 H.greenFunctionCrudeBound H.greenKernelLowerBound H.countingMeasureConvergence

/-- **Proposition 5.1** (`iDLALowerBound_final_of_strictGap`, 7fdfd3c and fb05dfd: through Lemmas 5.2-5.4 and their
forms on `V^ε(Λ_t)`, E-c1-5). -/
theorem iDLALowerBound (H : MainHypotheses 𝒮) : IDLALowerBoundStmt 𝒮 :=
  iDLALowerBound_final_of_strictGap 𝒮 H.volumeGrowth H.cellSizeEstimate H.countingMeasureConvergence
    H.greenFunctionCrudeBound H.greenKernelLowerBound H.exitTimeUpperBound H.convergenceDivisible
    H.coneHarmonicBalls H.coneHarmonicBallsUpToFixedTime H.uniformConvergenceGreenKernel H.boundedExitTimeRV
    (discreteLaplacianBoundCorrected 𝒮) H.coneFamilyAEMeasurable (LQGMeasureField.lqgMeasureFieldMeasurableStep 𝒮)
    H.meanValueSurplusLower H.harmonicBallStrictObstacleGap H.stoppedMeanValueInequality H.stoppedLLowerBound


/-! ## Section 6 -/

/-- **Lemma 6.5** (`annulusHit_of_volumeTail`). -/
theorem annulusHit (H : MainHypotheses 𝒮) : AnnulusHitStmt :=
  annulusHit_of_volumeTail H.wholePlaneLQGExistence H.coneWholePlaneWeylComparison H.wholePlaneLQGCoordinateChange
    H.wholePlaneUpperVolumeTail

/-- **Lemma 6.4** (`goodAnnulusPrevalence_of_annulusHit`; Lemma 6.6 `annulusIterate` proved, used inside). -/
theorem goodAnnulusPrevalence (H : MainHypotheses 𝒮) : GoodAnnulusPrevalenceStmt :=
  goodAnnulusPrevalence_of_annulusHit H.annulusHit H.coneMeanZeroRestriction
    Field.ConeCircle.circleAverageModConstStep

/-- **Lemma 6.8**, E-A10 (b) form (`constantOrderLowerBoundDiv_of_inputs`). -/
theorem constantOrderLowerBoundDivLog (H : MainHypotheses 𝒮) : ConstantOrderLowerBoundDivLogStmt 𝒮 :=
  constantOrderLowerBoundDiv_of_inputs 𝒮 H.greenKernelLowerBound H.volumeGrowth H.cellSizeEstimate
    H.countingMeasureConvergence H.exitTimeUpperBound H.goodAnnulusPrevalence
    (LQGMeasureField.lqgMeasureFieldMeasurableStep 𝒮)

/-- **Lemma 6.7**, E-A10 (b) form (`MatedCRT.constantOrderLowerBoundLog`). -/
theorem constantOrderLowerBoundLog (H : MainHypotheses 𝒮) : ConstantOrderLowerBoundLogStmt 𝒮 := by
  have h68 := H.constantOrderLowerBoundDivLog
  have h27 := H.volumeGrowth
  have h28 := H.cellSizeEstimate
  have h219 := H.expectedExitTimeExplicitBound
  have hcell := adjacentCellsMeetAeStep 𝒮
  apply _root_.MatedCRT.constantOrderLowerBoundLog <;> assumption

/-- **Lemma 6.9**, E-A10 (b) form (`chanceOfBeingAbsorbedLogLoss_of_steps`, with `Absorption.absorptionChernoffStep`). -/
theorem chanceOfBeingAbsorbedLogLoss (H : MainHypotheses 𝒮) : ChanceOfBeingAbsorbedLogLossStmt 𝒮 := by
  have h67 := H.constantOrderLowerBoundLog
  have hC : AbsorptionChernoffStep := Absorption.absorptionChernoffStep
  apply chanceOfBeingAbsorbedLogLoss_of_steps <;> assumption

/-- **Lemma 6.10** (`MatedCRT.iterativeBound`, with `AdjacentCellsMeetAeStep.probTendsToOne`). -/
theorem iterativeBound (H : MainHypotheses 𝒮) : IterativeBoundStmt 𝒮 := by
  have h69 := H.chanceOfBeingAbsorbedLogLoss
  have h28 := H.cellSizeEstimate
  have hA : AdjacentCellsMeetStep 𝒮 := by
    apply AdjacentCellsMeetAeStep.probTendsToOne
    exact adjacentCellsMeetAeStep 𝒮
  apply _root_.MatedCRT.iterativeBound <;> assumption

/-- **Proposition 6.1** (`IDLAUpperBound.iDLAUpperBound_of_steps`, the boundary-layer measurability from
`boundaryLayerMeasurableStep_of_coneFamilyAEMeasurable`). -/
theorem iDLAUpperBound (H : MainHypotheses 𝒮) : IDLAUpperBoundStmt 𝒮 :=
  IDLAUpperBound.iDLAUpperBound_of_steps 𝒮 H.iterativeBound H.iDLALowerBound
    (boundaryLayerMeasurableStep_of_coneFamilyAEMeasurable 𝒮 H.coneFamilyAEMeasurable H.coneHarmonicBallsUpToFixedTime)
    H.coneFamilyAEMeasurable H.coneHarmonicBallsUpToFixedTime

/-! ## Section 7 -/

/-- **Lemma 7.2**, corrected form (E-c3-2; `massBoundOdometerAboveScale_of_corrected`, on Lemma 4.4 corrected). -/
theorem massBoundOdometerAboveScale (H : MainHypotheses 𝒮) : MassBoundOdometerAboveScaleStmt 𝒮 :=
  massBoundOdometerAboveScale_of_corrected H.greenKernelLowerBound H.cellSizeEstimate
    (discreteLaplacianBoundCorrected 𝒮)

/-- **Lemma 7.3** (`odometerBoundMass_of_corrected`, on Lemma 4.4 corrected): proved. -/
theorem odometerBoundMass (𝒮 : SpaceFillingSLEModel) : OdometerBoundMassStmt 𝒮 :=
  odometerBoundMass_of_corrected (discreteLaplacianBoundCorrected 𝒮)

/-- **Lemma 7.4** (`crudeUpperBound_of_corrected`, on Lemma 4.4 corrected). -/
theorem crudeUpperBound (H : MainHypotheses 𝒮) : CrudeUpperBoundStmt 𝒮 :=
  crudeUpperBound_of_corrected (discreteLaplacianBoundCorrected 𝒮) H.degreeBound

/-- **Proposition 7.1** (`divSandpileUpperBound_of_meshScaling`, x2, d17f14c: the shell iteration from
`MepsScalingInput`; on Lemmas 6.8 (b) and 7.2 corrected). -/
theorem divSandpileUpperBound (H : MainHypotheses 𝒮) : DivSandpileUpperBoundStmt 𝒮 :=
  divSandpileUpperBound_of_meshScaling 𝒮 H.mepsScaling H.coneHarmonicBalls H.constantOrderLowerBoundDivLog
    H.volumeGrowth H.massBoundOdometerAboveScale H.convergenceDivisible H.uniformConvergenceGreenKernel
    H.cellSizeEstimate (odometerBoundMass 𝒮) H.crudeUpperBound

/-! ## Section 8 -/

/-- **Proposition 8.1** (`iDLAConstrainedConvergence_of_steps`). -/
theorem iDLAConstrainedConvergence (H : MainHypotheses 𝒮) : IDLAConstrainedConvergenceStmt 𝒮 :=
  iDLAConstrainedConvergence_of_steps 𝒮 H.divSandpileLowerBound H.iDLALowerBound H.iDLAUpperBound
    H.divSandpileUpperBound

end MainHypotheses

/-- **Theorem 1.4** (convergence of IDLA), conditional on `MainHypotheses 𝒮`: Proposition 8.1 and the scaling
argument of Section 8.1 (`convergenceOfIDLA_of_coneSteps`). -/
theorem convergenceOfIDLA_conditional (𝒮 : SpaceFillingSLEModel) (H : MainHypotheses 𝒮) :
    ConvergenceOfIDLAStmt 𝒮 :=
  convergenceOfIDLA_of_coneSteps 𝒮 H.iDLAConstrainedConvergence H.coneEnvironmentScaling H.quantumConeScaling
    H.lqgMeasureProperties H.coneHarmonicBallStrictGrowth H.coneHalfBallFamilyFunctional

/-- **Theorem 1.6** (convergence of the divisible sandpile), conditional on `MainHypotheses 𝒮`
(`convergenceOfDivSandpile_of_coneSteps`). -/
theorem convergenceOfDivSandpile_conditional (𝒮 : SpaceFillingSLEModel) (H : MainHypotheses 𝒮) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  convergenceOfDivSandpile_of_coneSteps 𝒮 H.iDLAConstrainedConvergence H.coneEnvironmentScaling
    H.quantumConeScaling H.lqgMeasureProperties H.coneHarmonicBallStrictGrowth H.coneHalfBallFamilyFunctional

end MatedCRT
