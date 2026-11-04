import MatedCRT.Assembly.Hypotheses
import MatedCRT.Steps.Sec1.Convergence
import MatedCRT.Steps.Sec8.IDLAConstrainedConvergence
import MatedCRT.Steps.Sec2.ConeHarmonicBalls
import MatedCRT.Steps.Sec2.MaximumPrinciple
import MatedCRT.Steps.Sec2.BoundedExitTimeRV
import MatedCRT.Steps.Sec2.ExpectedExitTimeExplicitBound
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Steps.Sec3.DiscretePotentialTightness
import MatedCRT.Steps.Sec3.ConvergenceHarmonicFunctions
import MatedCRT.Steps.Sec3.UniformConvergenceGreenKernel
import MatedCRT.Steps.Sec3.DiscreteDirichletProblem
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.OfSteps
import MatedCRT.Proofs.Sec4.ObstacleSpecialization
import MatedCRT.Proofs.Sec4.ObstacleSpecialization.GreenMarkov
import MatedCRT.Proofs.Sec4.Equibounded
import MatedCRT.Steps.Sec4.SubsequentialConvergence
import MatedCRT.Steps.Sec4.SubsequentialProperties
import MatedCRT.Steps.Sec4.ConvergenceDivisible
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.MaximumPrinciple
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.LocalExitReduction
import MatedCRT.Steps.Sec4.DivSandpileLowerBound
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.OdometerComparison
import MatedCRT.Steps.Sec5.MeanValueInequality
import MatedCRT.Steps.Sec5.IDLALowerBound
import MatedCRT.Proofs.Sec5.LLowerBound.OfEvents
import MatedCRT.Proofs.Sec5.MeanValueInequality.NormalizedStep
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.OfInteriorBoundary
import MatedCRT.Proofs.Measurability.EnvSigma
import MatedCRT.Steps.Sec6.AnnulusHit
import MatedCRT.Steps.Sec6.GoodAnnulusPrevalence
import MatedCRT.Proofs.Sec6.GoodAnnulusPrevalence.ConeTransfer
import MatedCRT.Proofs.Field.LawTransferComplete
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.OfSteps
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.LogLoss
import MatedCRT.Proofs.Sec6.ChanceOfBeingAbsorbed.Chernoff
import MatedCRT.Proofs.Sec6.ChanceOfBeingAbsorbed.LogLoss
import MatedCRT.Proofs.Sec6.IterativeBound.Statement
import MatedCRT.Proofs.Sec6.IDLAUpperBound.OfSteps
import MatedCRT.Steps.Sec7.DivSandpileUpperBound
import MatedCRT.Steps.Sec7.OdometerBoundMass
import MatedCRT.Steps.Sec7.CrudeUpperBound

/-!
# Theorems 1.4 and 1.6, conditional on the remaining hypotheses

`convergenceOfIDLA_conditional` and `convergenceOfDivSandpile_conditional` compose, by application only, the committed
reductions of the numbered results of "Internal DLA on mated-CRT maps" (arXiv:2211.04891) into Theorems 1.4 and 1.6,
under `MainHypotheses 𝒮` (MatedCRT/Assembly/Hypotheses.lean). Each numbered result on the way is one theorem
`MainHypotheses.<result>` below, proved by its reduction applied to the earlier results, to fields of `MainHypotheses`
and to proved steps; MatedCRT/Audit/Main.lean checks that every reduction is indeed used.

The main line: Theorems 1.4, 1.6 ← Proposition 8.1 (`iDLAConstrainedConvergence_of_steps`) ← Propositions 4.2, 5.1,
6.1, 7.1. Proved inputs discharged here: `adjacentCellsMeetAeStep` (IR-A2), Lemma 6.6 (`annulusIterate`),
`obstacleLimitUniqueness`, `greenKernelLaplacianStep`, `normExitTimeLaplacianStep`, `Absorption.absorptionChernoffStep`.

Corrected forms used where the Draft is false or open: 4.4 corrected (by 5.3), 3.1 corrected (by 3.5), the E-A10 (b)
log-loss forms of 6.7, 6.8, 6.9 (by 6.10). The Draft forms of 4.4, 3.1, 6.8, 7.2 still consumed by committed
reductions are group (d) of `MainHypotheses`. Lemma 7.2 corrected (`MassBoundOdometerAboveScaleStmt`) is not used:
Proposition 7.1 consumes the Draft 7.2, and its module cannot be imported with 7.1's (F6).

This file is regenerated as steps close; keep it mechanical.
-/

namespace MatedCRT

namespace MainHypotheses

variable {𝒮 : SpaceFillingSLEModel}

/-! ## Section 2 -/

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

/-- **Lemma 3.1**, corrected form (`discretePotentialTightness_of_steps`). -/
theorem discretePotentialTightnessCorrected (H : MainHypotheses 𝒮) : DiscretePotentialTightnessCorrectedStmt 𝒮 :=
  discretePotentialTightness_of_steps 𝒮 H.tightnessEquicontinuity H.tightnessSelection

/-- **Lemma 3.6** (`convergenceHarmonicFunctions_of_steps`). -/
theorem convergenceHarmonicFunctions (H : MainHypotheses 𝒮) : ConvergenceHarmonicFunctionsStmt 𝒮 :=
  convergenceHarmonicFunctions_of_steps 𝒮 H.randomWalkToLBM H.cellSizeEstimate H.harmonicPathExit
    H.harmonicExitCell

/-- **Lemma 3.3** (`uniformConvergenceGreenKernel_of_steps`; consumes the Draft 3.1). -/
theorem uniformConvergenceGreenKernel (H : MainHypotheses 𝒮) : UniformConvergenceGreenKernelStmt 𝒮 :=
  uniformConvergenceGreenKernel_of_steps 𝒮 H.degreeMeasureConvergence H.integralConvergenceGreenFunction
    H.greenKernelUpperBound H.cellSizeEstimate H.discretePotentialTightness (maximumPrinciple 𝒮)
    H.greenKernelInterior H.greenKernelBoundary

/-- **Lemma 3.5** (`discreteDirichletProblem_of_steps`). -/
theorem discreteDirichletProblem (H : MainHypotheses 𝒮) : DiscreteDirichletProblemStmt 𝒮 :=
  discreteDirichletProblem_of_steps 𝒮 H.greenPotentialHolder H.convergenceHarmonicFunctions
    H.integralConvergenceGreenFunction H.discretePotentialTightnessCorrected (maximumPrinciple 𝒮)
    H.expectedExitTimeExplicitBound H.cellSizeEstimate H.dirichletLimit H.dirichletInterior H.dirichletBoundary

/-- **Lemma 3.7** (`convergenceNormalizedExitTime_of_interior_discrete_boundary`; consumes the Draft 3.1). -/
theorem convergenceNormalizedExitTime (H : MainHypotheses 𝒮) : ConvergenceNormalizedExitTimeStmt 𝒮 := by
  have h33 := H.uniformConvergenceGreenKernel
  have h29 := H.countingMeasureConvergence
  have h219 := H.expectedExitTimeExplicitBound
  have h35 := H.discreteDirichletProblem
  have h31 := H.discretePotentialTightness
  have h28 := H.cellSizeEstimate
  have h217 := H.boundedExitTimeRV
  have hint := H.normalizedExitInterior
  have hbdry := H.discreteExitBoundary
  apply convergenceNormalizedExitTime_of_interior_discrete_boundary <;> assumption

/-! ## Section 4 -/

/-- **Lemma 4.3** (`discreteBasicProperties_of_inputs`). -/
theorem discreteBasicProperties (H : MainHypotheses 𝒮) : DiscreteBasicPropertiesStmt 𝒮 :=
  discreteBasicProperties_of_inputs greenKernelLaplacianStep normExitTimeLaplacianStep H.ballInteriorConnected
    (adjacentCellsMeetAeStep 𝒮)

/-- **Lemma 4.4**, corrected form (E-c1-1, `discreteLaplacianBoundCorrected_of_inputs`). -/
theorem discreteLaplacianBoundCorrected (H : MainHypotheses 𝒮) : DiscreteLaplacianBoundCorrectedStmt 𝒮 :=
  discreteLaplacianBoundCorrected_of_inputs greenKernelLaplacianStep H.ballInteriorConnected
    (adjacentCellsMeetAeStep 𝒮)

/-- **Lemma 4.7** (`equibounded_of_steps`). -/
theorem equibounded (H : MainHypotheses 𝒮) : EquiboundedStmt 𝒮 :=
  equibounded_of_steps H.discreteBasicProperties H.boundedExitTimeRV H.exitTimeUpperBound H.mepsScaling

/-- **Lemma 4.6** (`subsequentialConvergence_of_steps`; consumes the Draft 4.4 and the Draft 3.1). -/
theorem subsequentialConvergence (H : MainHypotheses 𝒮) : SubsequentialConvergenceStmt 𝒮 :=
  subsequentialConvergence_of_steps 𝒮 H.equibounded H.discreteLaplacianBound H.discretePotentialTightness
    H.discreteDirichletProblem H.odometerLocalCompactness H.odometerBoundaryUpgrade H.odometerMeasurableSelection

/-- **Lemma 4.8** (`subsequentialProperties_of_steps`; consumes the Draft 4.4). -/
theorem subsequentialProperties (H : MainHypotheses 𝒮) : SubsequentialPropertiesStmt 𝒮 :=
  subsequentialProperties_of_steps 𝒮 H.uniformConvergenceGreenKernel H.discreteDirichletProblem
    H.convergenceNormalizedExitTime H.subsequentialConvergence H.discreteBasicProperties H.discreteLaplacianBound
    (maximumPrinciple 𝒮) H.odometerObstacleApproximation H.odometerDistributionalLimit

/-- **Theorem 4.1** (`convergenceDivisible_of_steps`, with `obstacleLimitUniqueness`). -/
theorem convergenceDivisible (H : MainHypotheses 𝒮) : ConvergenceDivisibleStmt 𝒮 :=
  convergenceDivisible_of_steps 𝒮 H.subsequentialProperties H.subsequentialConvergence
    (obstacleLimitUniqueness 𝒮) H.convergenceDivisibleEventMeasurable

/-- **Proposition 4.2** (`divSandpileLowerBound_of_steps`, with `divSandpileOdometerComparison_of_cellsMeet`). -/
theorem divSandpileLowerBound (H : MainHypotheses 𝒮) : DivSandpileLowerBoundStmt 𝒮 :=
  divSandpileLowerBound_of_steps 𝒮 H.convergenceDivisible H.coneHarmonicBalls (maximumPrinciple 𝒮)
    H.uniformConvergenceGreenKernel H.cellSizeEstimate H.obstacleClusterInnerApproximation
    (divSandpileOdometerComparison_of_cellsMeet (adjacentCellsMeetAeStep 𝒮))

/-! ## Section 5 -/

/-- **Lemma 5.3** (`meanValueInequality_of_surplus`, on Lemma 4.4 corrected). -/
theorem meanValueInequality (H : MainHypotheses 𝒮) : MeanValueInequalityStmt 𝒮 := by
  have h44 := H.discreteLaplacianBoundCorrected
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

/-- The discrete-cluster form of Proposition 4.2 used by Proposition 5.1 (`discreteClusterInnerBound_of_steps`). -/
theorem discreteClusterInnerBound (H : MainHypotheses 𝒮) : DiscreteClusterInnerBoundStep 𝒮 :=
  discreteClusterInnerBound_of_steps 𝒮 H.obstacleClusterInnerApproximation H.convergenceDivisible
    H.coneHarmonicBalls (maximumPrinciple 𝒮) H.uniformConvergenceGreenKernel H.cellSizeEstimate

/-- **Proposition 5.1** (`iDLALowerBound_of_volumeGrowth_cellSize`, through Lemma 5.2; `σ(h, η)` is null-measurable,
so no measurability step remains). -/
theorem iDLALowerBound (H : MainHypotheses 𝒮) : IDLALowerBoundStmt 𝒮 :=
  iDLALowerBound_of_volumeGrowth_cellSize 𝒮 H.volumeGrowth H.cellSizeEstimate H.meanValueInequality
    H.lLowerBound H.discreteClusterInnerBound H.iDLALowerBoundStopped

/-! ## Section 6 -/

/-- **Lemma 6.5** (`annulusHit_of_steps`). -/
theorem annulusHit (H : MainHypotheses 𝒮) : AnnulusHitStmt :=
  annulusHit_of_steps H.wholePlaneLQGExistence H.coneWholePlaneWeylComparison H.wholePlaneLQGCoordinateChange
    H.wholePlaneGoodAnnulusTightness

/-- **Lemma 6.4** (`goodAnnulusPrevalence_of_steps`, with Lemma 6.6 `annulusIterate` proved and the cone transfer
`annulusIterateConeTransfer`). -/
theorem goodAnnulusPrevalence (H : MainHypotheses 𝒮) : GoodAnnulusPrevalenceStmt :=
  goodAnnulusPrevalence_of_steps annulusIterate H.annulusHit (annulusIterateConeTransfer H.coneMeanZeroRestriction)
    H.goodAnnulusEventLocality

/-- **Lemma 6.8**, E-A10 (b) form (`constantOrderLowerBoundDiv_of_steps`). -/
theorem constantOrderLowerBoundDivLog (H : MainHypotheses 𝒮) : ConstantOrderLowerBoundDivLogStmt 𝒮 := by
  have h216 := H.greenKernelLowerBound
  have h27 := H.volumeGrowth
  have h28 := H.cellSizeEstimate
  have h29 := H.countingMeasureConvergence
  have h64 := H.goodAnnulusPrevalence
  have h218 := H.exitTimeUpperBound
  have h219 := H.expectedExitTimeExplicitBound
  have hmeas := H.goodScaleEventMeasurable
  have hcell := adjacentCellsMeetAeStep 𝒮
  apply constantOrderLowerBoundDiv_of_steps <;> assumption

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

/-- **Proposition 6.1** (`IDLAUpperBound.iDLAUpperBound_of_steps`). -/
theorem iDLAUpperBound (H : MainHypotheses 𝒮) : IDLAUpperBoundStmt 𝒮 :=
  IDLAUpperBound.iDLAUpperBound_of_steps 𝒮 H.iterativeBound H.iDLALowerBound H.boundaryLayerMeasurable

/-! ## Section 7 -/

/-- **Lemma 7.3** (`odometerBoundMass_of_draft`; consumes the Draft 4.4). -/
theorem odometerBoundMass (H : MainHypotheses 𝒮) : OdometerBoundMassStmt 𝒮 := by
  have h44 := H.discreteLaplacianBound
  have hcell := adjacentCellsMeetAeStep 𝒮
  apply odometerBoundMass_of_draft <;> assumption

/-- **Lemma 7.4** (`crudeUpperBound_of_draft`; consumes the Draft 4.4). -/
theorem crudeUpperBound (H : MainHypotheses 𝒮) : CrudeUpperBoundStmt 𝒮 := by
  have h44 := H.discreteLaplacianBound
  have hdeg := H.degreeBound
  have hcell := adjacentCellsMeetAeStep 𝒮
  apply crudeUpperBound_of_draft <;> assumption

/-- **Proposition 7.1** (`divSandpileUpperBound_of_carved_inputs`, the shell confinement from
`stoppedShellConfinement_of_intermediateShell` and `intermediateShell_of_shellIteration`; consumes the Draft 6.8 and
the Draft 7.2). -/
theorem divSandpileUpperBound (H : MainHypotheses 𝒮) : DivSandpileUpperBoundStmt 𝒮 :=
  divSandpileUpperBound_of_carved_inputs 𝒮 H.coneHarmonicBalls H.constantOrderLowerBoundDiv H.volumeGrowth
    H.massBoundOdometer H.convergenceDivisible H.uniformConvergenceGreenKernel H.cellSizeEstimate
    H.odometerBoundMass H.crudeUpperBound H.stoppedObstacleSetup
    (stoppedShellConfinement_of_intermediateShell 𝒮 (intermediateShell_of_shellIteration 𝒮 H.shellIteration))

/-! ## Section 8 -/

/-- **Proposition 8.1** (`iDLAConstrainedConvergence_of_steps`). -/
theorem iDLAConstrainedConvergence (H : MainHypotheses 𝒮) : IDLAConstrainedConvergenceStmt 𝒮 :=
  iDLAConstrainedConvergence_of_steps 𝒮 H.divSandpileLowerBound H.iDLALowerBound H.iDLAUpperBound
    H.divSandpileUpperBound

end MainHypotheses

/-- **Theorem 1.4** (convergence of IDLA), conditional on `MainHypotheses 𝒮`: Proposition 8.1 and the scaling
argument of Section 8.1 (`convergenceOfIDLA_of_steps`). See the warning on `MainHypotheses` (group (d)). -/
theorem convergenceOfIDLA_conditional (𝒮 : SpaceFillingSLEModel) (H : MainHypotheses 𝒮) :
    ConvergenceOfIDLAStmt 𝒮 :=
  convergenceOfIDLA_of_steps 𝒮 H.iDLAConstrainedConvergence H.coneEnvironmentScaling H.harmonicBallFamilyScaling
    H.coneScaleRadius H.scaledClusterExitTime

/-- **Theorem 1.6** (convergence of the divisible sandpile), conditional on `MainHypotheses 𝒮`
(`convergenceOfDivSandpile_of_steps`). See the warning on `MainHypotheses` (group (d)). -/
theorem convergenceOfDivSandpile_conditional (𝒮 : SpaceFillingSLEModel) (H : MainHypotheses 𝒮) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  convergenceOfDivSandpile_of_steps 𝒮 H.iDLAConstrainedConvergence H.coneEnvironmentScaling
    H.harmonicBallFamilyScaling H.coneScaleRadius H.scaledClusterExitTime

end MatedCRT
