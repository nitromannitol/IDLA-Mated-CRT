import MatedCRT
import MatedCRT.Steps.Sec1.Convergence
import MatedCRT.Steps.Sec2.ConeHarmonicBalls
import MatedCRT.Steps.Sec3.DiscretePotentialTightness
import MatedCRT.Steps.Sec3.UniformConvergenceGreenKernel
import MatedCRT.Steps.Sec3.DiscreteDirichletProblem
import MatedCRT.Steps.Sec3.ConvergenceHarmonicFunctions
import MatedCRT.Steps.Sec3.ConvergenceNormalizedExitTime
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.OfInteriorBoundary
import MatedCRT.Steps.Sec4.ConvergenceDivisible
import MatedCRT.Proofs.Sec5.MeanValueInequality.NormalizedStep
import MatedCRT.Steps.Sec4.DivSandpileLowerBound
import MatedCRT.Steps.Sec4.ObstacleSpecialization
import MatedCRT.Steps.Sec4.SubsequentialConvergence
import MatedCRT.Steps.Sec4.SubsequentialProperties
import MatedCRT.Steps.Sec5.GeneralIDLALowerBound
import MatedCRT.Steps.Sec5.IDLALowerBound
import MatedCRT.Steps.Sec5.MeanValueInequality
import MatedCRT.Proofs.Sec5.LLowerBound.GreenSum
import MatedCRT.Steps.Sec6.IDLAUpperBound
import MatedCRT.Steps.Sec6.ConstantOrderLowerBoundDiv
import MatedCRT.Steps.Sec6.GoodAnnulusPrevalence
import MatedCRT.Steps.Sec6.AnnulusHit
import MatedCRT.Steps.Sec7.DivSandpileUpperBound

/-!
# The remaining hypotheses of Theorems 1.4 and 1.6

`MainHypotheses 𝒮` collects, one field per Prop, every hypothesis that the committed reductions of the numbered results
of "Internal DLA on mated-CRT maps" (Bou-Rabee and Gwynne, arXiv:2211.04891) still need in order to give Theorems 1.4
and 1.6 (`convergenceOfIDLA_conditional`, `convergenceOfDivSandpile_conditional`, MatedCRT/Assembly/Main.lean). A
proved step or a proved numbered result is not a field: it is discharged in Main.lean.

The fields are grouped:
* (a) cited results of the paper (Draft statements of results the paper quotes from the literature), and the
  statement of [BG22] the paper cites from the harmonic-balls formalization;
* (b) literature inputs (`...Input`, MatedCRT/External);
* (c) open named steps (`...Step`, MatedCRT/Steps), with their owner from STATUS.md and tasks/*.md (2026-11-04);
* (d) Draft statements awaiting an operator ruling: they are false or open as drafted, no reduction proves them, and a
  committed reduction on the main line still consumes the Draft form;
* (e) paper-owned numbered results with no committed reduction yet.

This file is regenerated as steps close: a field disappears when its Prop is proved or reduced.
-/

namespace MatedCRT

/-- The remaining hypotheses of the conditional proof of Theorems 1.4 and 1.6 for the space-filling SLE model `𝒮`.
Field counts: (a) 10, (b) 2, (c) 36, (d) 4, (e) 3.

WARNING: as long as group (d) holds the Draft forms of Lemmas 4.4 (E-c1-1), 3.1 (E-c1-4), 7.2 (E-c3-2, refuted) and
6.8 (E-A10 (b)), which are reported false as drafted, this structure is expected to be unsatisfiable and the
conditional theorems are vacuous. They become meaningful once the consumers (4.6, 4.8, 3.3, 3.7, 7.1, 7.3, 7.4) are
rerouted through the corrected forms, or the operator replaces the Draft statements. -/
structure MainHypotheses (𝒮 : SpaceFillingSLEModel) : Prop where
  -- (a) Cited results
  /-- **Lemma 2.7** (cited, volume growth of cells). Used by 2.17, 5.1, 6.7 (b), 6.8 (b), 7.1. -/
  volumeGrowth : VolumeGrowthStmt
  /-- **Lemma 2.8** (cited, cell size estimate). -/
  cellSizeEstimate : CellSizeEstimateStmt 𝒮
  /-- **Lemma 2.9** (cited, convergence of the counting measure). Used by 3.7, 5.4, 6.8. -/
  countingMeasureConvergence : CountingMeasureConvergenceStmt 𝒮
  /-- **Lemma 2.10** (cited, convergence of the degree measure). Used by 3.3. -/
  degreeMeasureConvergence : DegreeMeasureConvergenceStmt 𝒮
  /-- **Theorem 2.11** (cited, random walk on the mated-CRT map converges to Liouville Brownian motion). Used by 3.6. -/
  randomWalkToLBM : RandomWalkToLBMStmt 𝒮
  /-- **Lemma 2.14** (cited, upper bound for the Green kernel). Used by 3.3. -/
  greenKernelUpperBound : GreenKernelUpperBoundStmt 𝒮
  /-- **Lemma 2.15** (cited, crude bound for the Green function). Used by 5.4. -/
  greenFunctionCrudeBound : GreenFunctionCrudeBoundStmt 𝒮
  /-- **Lemma 2.16** (cited, lower bound for the Green kernel). Used by 5.4, 6.8. -/
  greenKernelLowerBound : GreenKernelLowerBoundStmt 𝒮
  /-- **Lemma 2.18** (cited, exit time upper bound). Used by 2.19, 4.7, 5.3, 6.8. -/
  exitTimeUpperBound : ExitTimeUpperBoundStmt 𝒮
  /-- Hölder continuity of LQG Green potentials, the [BG22] statement cited in the proof of Lemma 3.5
  (`HarmonicBalls.GreenPotentialHolderStmt`, harmonic-balls Draft Section 2). -/
  greenPotentialHolder : _root_.HarmonicBalls.GreenPotentialHolderStmt.{0}
  -- (b) Literature inputs
  /-- `MepsScalingInput` (External/SLE.lean): scaling of the expected exit time, used by Lemma 4.7. -/
  mepsScaling : MepsScalingInput 𝒮
  /-- `DegreeBoundInput` (External/SLE.lean): degree bound of the mated-CRT map, used by Lemma 7.4. -/
  degreeBound : DegreeBoundInput 𝒮
  -- (c) Open named steps
  /-- Theorems 1.4, 1.6 from Proposition 8.1: the rescaled environment is valid (eq:scale-invariance-of-field-and-eta).
  Owner: unassigned (carved by c3, Steps/Sec1/Convergence.lean). -/
  coneEnvironmentScaling : ConeEnvironmentScalingStep 𝒮
  /-- Theorems 1.4, 1.6: deterministic covariance of the harmonic-ball conditions under scaling. Owner: unassigned
  (carved by c3). -/
  harmonicBallFamilyScaling : HarmonicBallFamilyScalingStep
  /-- Theorems 1.4, 1.6: the cone scale radius `R_b` is an a.s. positive random variable. Owner: unassigned (c3). -/
  coneScaleRadius : ConeScaleRadiusStep
  /-- Theorems 1.4, 1.6: eq:btb-converge-to-inf, `P[b T^b ≤ t] → 0`. Owner: unassigned (c3). -/
  scaledClusterExitTime : ScaledClusterExitTimeStep
  /-- Theorem 2.3: the families of Lemmas 2.4, 2.5 are random variables. Owner: A. -/
  coneFamilyAEMeasurable : ConeFamilyAEMeasurableStep
  /-- Lemma 3.1 (corrected form): asymptotic equicontinuity. Owner: c1. -/
  tightnessEquicontinuity : TightnessEquicontinuityStep 𝒮
  /-- Lemma 3.1 (corrected form): measurable selection of a convergent subsequence. Owner: c1. -/
  tightnessSelection : TightnessSelectionStep 𝒮
  /-- Lemma 3.3: interior estimate. Owner: m1. -/
  greenKernelInterior : GreenKernelInteriorStep 𝒮
  /-- Lemma 3.3: boundary estimate. Owner: m1. -/
  greenKernelBoundary : GreenKernelBoundaryStep 𝒮
  /-- Lemma 3.5: identification of the limit. Owner: m1. -/
  dirichletLimit : DirichletLimitStep 𝒮
  /-- Lemma 3.5: interior estimate. Owner: m1. -/
  dirichletInterior : DirichletInteriorStep 𝒮
  /-- Lemma 3.5: boundary estimate. Owner: m1. -/
  dirichletBoundary : DirichletBoundaryStep 𝒮
  /-- Lemma 3.6: exit of the Liouville Brownian path. Owner: m2. -/
  harmonicPathExit : HarmonicPathExitStep 𝒮
  /-- Lemma 3.6: the exit cell. Owner: m2. -/
  harmonicExitCell : HarmonicExitCellStep 𝒮
  /-- Lemma 3.7 (`convergenceNormalizedExitTime_of_interior_discrete_boundary`): interior estimate. Owner: x1. -/
  normalizedExitInterior : NormalizedExitInteriorStep 𝒮
  /-- Lemma 3.7: boundary estimate for the discrete exit time. Owner: x1. -/
  discreteExitBoundary : DiscreteExitBoundaryStep 𝒮
  /-- Theorem 4.1: measurability of the convergence event (F8: reduced only to unnamed hypotheses). Owner: x3. -/
  convergenceDivisibleEventMeasurable : ConvergenceDivisibleEventMeasurableStep 𝒮
  /-- Proposition 4.2 and Proposition 5.1 (discrete-cluster form of 4.2): inner approximation of the obstacle
  cluster. Owner: x3. -/
  obstacleClusterInnerApproximation : ObstacleClusterInnerApproximationStep 𝒮
  /-- Lemmas 4.3, 4.4 (corrected): connectivity of the ball interior (E-c1-2). Owner: c1. -/
  ballInteriorConnected : BallInteriorConnectedStep 𝒮
  /-- Lemma 4.6: local compactness of the odometers. Owner: x3. -/
  odometerLocalCompactness : OdometerLocalCompactnessStep 𝒮
  /-- Lemma 4.6: boundary upgrade. Owner: x3. -/
  odometerBoundaryUpgrade : OdometerBoundaryUpgradeStep 𝒮
  /-- Lemma 4.6: measurable selection of the subsequence. Owner: x3. -/
  odometerMeasurableSelection : OdometerMeasurableSelectionStep 𝒮
  /-- Lemma 4.8: the limit solves the obstacle problem. Owner: x3. -/
  odometerObstacleApproximation : OdometerObstacleApproximationStep 𝒮
  /-- Lemma 4.8: distributional limit of the Laplacians. Owner: x3. -/
  odometerDistributionalLimit : OdometerDistributionalLimitStep 𝒮
  /-- Proposition 5.1: the stopped form, not given by the printed proof. Owner: c2. -/
  iDLALowerBoundStopped : IDLALowerBoundStoppedStep 𝒮
  /-- Lemma 5.3 (`meanValueInequality_of_surplus`): the surplus step (E-x1-1). Owner: x1. -/
  meanValueSurplus : MeanValueSurplusStep 𝒮
  /-- Proposition 6.1: measurability of the boundary layer event. Owner: c2. -/
  boundaryLayerMeasurable : BoundaryLayerMeasurableStep 𝒮
  /-- Lemma 6.8 (E-A10 (b) form): measurability of the good scale events. Owner: c4. -/
  goodScaleEventMeasurable : GoodScaleEventMeasurableStep 𝒮
  /-- Lemma 6.4 (through `annulusIterateConeTransfer`, IR-c4-5): restriction of the cone field to annuli has mean
  zero. Owner: c4. -/
  coneMeanZeroRestriction : ConeMeanZeroRestrictionStep
  /-- Lemma 6.4: locality of the good annulus events (IR-c4-6). Owner: c4. -/
  goodAnnulusEventLocality : GoodAnnulusEventLocalityStep
  /-- Lemma 6.5: existence of the whole-plane LQG objects (IR-c4-1). Owner: c4. -/
  wholePlaneLQGExistence : WholePlaneLQGExistenceStep
  /-- Lemma 6.5: Weyl comparison of the cone and whole-plane fields (IR-c4-2). Owner: c4. -/
  coneWholePlaneWeylComparison : ConeWholePlaneWeylComparisonStep
  /-- Lemma 6.5: coordinate change (IR-c4-3). Owner: c4. -/
  wholePlaneLQGCoordinateChange : WholePlaneLQGCoordinateChangeStep
  /-- Lemma 6.5: tightness of the good annulus events (IR-c4-4). Owner: c4. -/
  wholePlaneGoodAnnulusTightness : WholePlaneGoodAnnulusTightnessStep
  /-- Proposition 7.1: setup of the stopped obstacle problem. Owner: x2. -/
  stoppedObstacleSetup : StoppedObstacleSetupStep 𝒮
  /-- Proposition 7.1 (through `intermediateShell_of_shellIteration`, `stoppedShellConfinement_of_intermediateShell`):
  the shell iteration. Owner: x2. -/
  shellIteration : ShellIterationStep 𝒮
  -- (d) Draft statements awaiting an operator ruling
  /-- **Lemma 4.4**, Draft form (OPEN, E-c1-1: false for large `ε`). Consumed by 4.6, 4.8 (x3) and 7.3, 7.4 (through
  `stoppedOdometerLaplacianStep_of_draft`); only the corrected form `DiscreteLaplacianBoundCorrectedStmt` is proved
  (used here by 5.3). -/
  discreteLaplacianBound : DiscreteLaplacianBoundStmt 𝒮
  /-- **Lemma 3.1**, Draft form (E-c1-4: false for closed `D`; chk N1: the Hölder hypothesis must be `C' ε⁻¹`).
  Consumed by 3.3, 3.7, 4.6; only `DiscretePotentialTightnessCorrectedStmt` is reduced (used here by 3.5). -/
  discretePotentialTightness : DiscretePotentialTightnessStmt 𝒮
  /-- **Lemma 6.8**, Draft form without log loss (E-A10 (b): only the log-loss form `ConstantOrderLowerBoundDivLogStmt`
  is reduced, used here by 6.7 (b)-6.10). Consumed by Proposition 7.1 (x2). -/
  constantOrderLowerBoundDiv : ConstantOrderLowerBoundDivStmt 𝒮
  /-- **Lemma 7.2**, Draft form (REFUTED, E-c3-2: false for `s` below the cell scale). Consumed by Proposition 7.1 (x2);
  only `MassBoundOdometerAboveScaleStmt` (`s ≥ ε^β`) is reduced, and its module cannot be imported together with 7.1's
  (F6, `MatedCRT.Sec7.vertexPoint_mem_cell`). With this field `MainHypotheses` is unsatisfiable until 7.1 is rerouted. -/
  massBoundOdometer : MassBoundOdometerStmt 𝒮
  -- (e) Paper-owned results with no committed reduction
  /-- **Lemma 2.4** (harmonic balls of the cone up to a fixed time). Owner: A (Steps/Sec2 untracked). -/
  coneHarmonicBallsUpToFixedTime : ConeHarmonicBallsUpToFixedTimeStmt
  /-- **Lemma 2.5** (scale invariance up to a fixed time). Owner: A. -/
  coneScaleInvarianceUpToFixedTime : ConeScaleInvarianceUpToFixedTimeStmt
  /-- **Lemma 3.4** (convergence of integrals of the Green function). Owner: m2. Used by 3.3, 3.5. -/
  integralConvergenceGreenFunction : IntegralConvergenceGreenFunctionStmt 𝒮

end MatedCRT
