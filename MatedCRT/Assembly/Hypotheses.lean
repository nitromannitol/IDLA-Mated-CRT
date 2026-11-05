import MatedCRT
import MatedCRT.Proofs.Sec1.Main
import MatedCRT.Proofs.Measurability.ConeScaleInputs
import MatedCRT.Proofs.Sec2.Final
import MatedCRT.Steps.Sec2.ConeHarmonicBallsUpToFixedTime
import MatedCRT.Steps.Sec2.ConeHarmonicBalls
import MatedCRT.Steps.Sec3.DiscretePotentialTightness
import MatedCRT.Steps.Sec3.UniformConvergenceGreenKernel
import MatedCRT.Steps.Sec3.DiscreteDirichletProblem
import MatedCRT.Steps.Sec3.ConvergenceHarmonicFunctions
import MatedCRT.Steps.Sec3.ConvergenceNormalizedExitTime
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.OfInteriorBoundary
import MatedCRT.Steps.Sec4.ConvergenceDivisible
import MatedCRT.Steps.Sec4.DivSandpileLowerBound
import MatedCRT.Proofs.Sec4.SubsequentialConvergence.Corrected
import MatedCRT.Proofs.Sec4.SubsequentialProperties.Corrected
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.Final
import MatedCRT.Steps.Sec5.IDLALowerBound
import MatedCRT.Steps.Sec5.MeanValueInequality
import MatedCRT.Proofs.Sec5.MeanValueInequality.SurplusSteps
import MatedCRT.Proofs.Sec5.IDLALowerBound.Final
import MatedCRT.Steps.Sec6.IDLAUpperBound
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Final
import MatedCRT.Proofs.Sec6.AnnulusHit.Main
import MatedCRT.Proofs.Sec6.GoodAnnulusPrevalence.Main
import MatedCRT.Steps.Sec7.DivSandpileUpperBound

/-!
# The remaining hypotheses of Theorems 1.4 and 1.6

`MainHypotheses 𝒮` collects, one field per Prop, every hypothesis that the committed reductions of the numbered results
of "Internal DLA on mated-CRT maps" (Bou-Rabee and Gwynne, arXiv:2211.04891) still need in order to give Theorems 1.4
and 1.6 (`convergenceOfIDLA_conditional`, `convergenceOfDivSandpile_conditional`, MatedCRT/Assembly/Main.lean). A
proved step or a proved numbered result is not a field: it is discharged in Main.lean.

The fields are grouped:
* (a) cited results of the paper (Draft statements of results the paper quotes from the literature), and the
  statements of [BG22] the paper cites, from the harmonic-balls formalization;
* (b) literature inputs (`...Input`, MatedCRT/External);
* (c) open named steps (`...Step`), with their owner (tasks of 2026-11-05 06:00Z);
* (d) statements awaiting an operator ruling: a Draft reported false as drafted that a committed reduction still
  consumes, a corrected cited statement whose admission is pending, and a corrected form of a frozen statement;
* (e) paper-owned numbered results with no committed reduction yet.

No field is a Draft statement refuted in Lean (MatedCRT/Audit/Main.lean checks this against MatedCRT/Audit/*).
This file is regenerated as steps close: a field disappears when its Prop is proved or reduced.
-/

namespace MatedCRT

/-- The remaining hypotheses of the conditional proof of Theorems 1.4 and 1.6 for the space-filling SLE model `𝒮`.
Field counts: (a) 12, (b) 3, (c) 27, (d) 3, (e) 1; total 46.

WARNING: group (d) holds the Draft Lemma 3.1 (`DiscretePotentialTightnessStmt`), reported false for non-open `D`
(ESCALATIONS E-c1-4). If that report is right, this structure is unsatisfiable and the conditional theorems are vacuous
until its last consumer, Lemma 3.3 (m1), is rerouted through a corrected form or the operator replaces the Draft. -/
structure MainHypotheses (𝒮 : SpaceFillingSLEModel) : Prop where
  -- (a) Cited results
  /-- **Fact 2.2** (cited, properties of the LQG measure, DS11). Used by 1.4, 1.6, 2.3 (through 2.5). -/
  lqgMeasureProperties : LQGMeasurePropertiesStmt
  /-- **Lemma 2.7** (cited, volume growth of cells). Used by 2.17, 3.1 (corrected), 4.1, 5.1, 6.8 (b), 7.1. -/
  volumeGrowth : VolumeGrowthStmt
  /-- **Lemma 2.8** (cited, cell size estimate). -/
  cellSizeEstimate : CellSizeEstimateStmt 𝒮
  /-- **Lemma 2.9** (cited, convergence of the counting measure). Used by 5.1 (through 5.4), 6.8 (b). -/
  countingMeasureConvergence : CountingMeasureConvergenceStmt 𝒮
  /-- **Lemma 2.10** (cited, convergence of the degree measure). Used by 3.3. -/
  degreeMeasureConvergence : DegreeMeasureConvergenceStmt 𝒮
  /-- **Theorem 2.11** (cited, random walk on the mated-CRT map converges to Liouville Brownian motion). Used by 3.6. -/
  randomWalkToLBM : RandomWalkToLBMStmt 𝒮
  /-- **Lemma 2.14** (cited, upper bound for the Green kernel). Used by 3.3. -/
  greenKernelUpperBound : GreenKernelUpperBoundStmt 𝒮
  /-- **Lemma 2.15** (cited, crude bound for the Green function). Used by 5.1 (through 5.4). -/
  greenFunctionCrudeBound : GreenFunctionCrudeBoundStmt 𝒮
  /-- **Lemma 2.16** (cited, lower bound for the Green kernel). Used by 5.1, 6.8 (b), 7.2 (corrected). -/
  greenKernelLowerBound : GreenKernelLowerBoundStmt 𝒮
  /-- **Lemma 2.18** (cited, exit time upper bound). Used by 2.19, 3.1 (corrected), 3.7, 4.7, 5.1, 6.8 (b). -/
  exitTimeUpperBound : ExitTimeUpperBoundStmt 𝒮
  /-- Hölder continuity of LQG Green potentials, the [BG22] statement cited in the proof of Lemma 3.5
  (`HarmonicBalls.GreenPotentialHolderStmt`, harmonic-balls Draft Section 2). -/
  greenPotentialHolder : _root_.HarmonicBalls.GreenPotentialHolderStmt.{0}
  /-- The [BG22] statements on harmonic balls cited in Section 2 (harmonic-balls Drafts: Theorem 1.1, Theorem 5.5,
  Proposition 5.6, Lemmas 3.1-3.5, Propositions 5.2, 5.3, Lemma 5.8; `HarmonicBallsDraftInputs`). Used by 2.4. -/
  harmonicBallsDraftInputs : HarmonicBallsDraftInputs
  -- (b) Literature inputs
  /-- `MepsScalingInput` (External/SLE.lean): scaling of the expected exit time, used by 3.1 (corrected), 4.7, 7.1. -/
  mepsScaling : MepsScalingInput 𝒮
  /-- `DegreeBoundInput` (External/SLE.lean): degree bound of the mated-CRT map, used by Lemma 7.4. -/
  degreeBound : DegreeBoundInput 𝒮
  /-- `QuantumConeScalingInput` (External/QuantumCone.lean): scale invariance of the `γ`-quantum cone, used by 1.4,
  1.6, 2.3 (through 2.5 and the measurability of its families). -/
  quantumConeScaling : QuantumConeScalingInput
  -- (c) Open named steps
  /-- Theorems 1.4, 1.6: the rescaled environment is valid (eq:scale-invariance-of-field-and-eta, IR-c3-1). Reduced
  (`coneEnvironmentScalingStep_of_inputs`, c1, 0d13527) to External SLE inputs and the requested, not yet admitted,
  `RescaledEnvironmentInput` (IR-c1-1). Owner: c1 / operator (IR-c1-1). -/
  coneEnvironmentScaling : ConeEnvironmentScalingStep 𝒮
  /-- Lemma 2.4: existence of the whole-plane log-singular LQG objects. Owner: c2. -/
  wholePlaneLogLQGExistence : WholePlaneLogLQGExistenceStep
  /-- Lemma 2.4: restriction to the cone. Owner: c2. -/
  coneRestriction : ConeRestrictionStep
  /-- Lemma 2.4: locality of the cone harmonic balls. Owner: c2. -/
  coneHarmonicBallLocality : ConeHarmonicBallLocalityStep
  /-- Lemmas 2.4, 2.5, Theorems 1.4, 1.6: strict growth of the cone harmonic balls (`T' = T`, E-c5-3, not in the
  paper). Owner: c2 / operator (E-c5-3: admit as an External input?). -/
  coneHarmonicBallStrictGrowth : ConeHarmonicBallStrictGrowthStep
  /-- Lemma 2.5, Theorems 1.4, 1.6: the half-ball family is a functional of the field. Owner: c2. -/
  coneHalfBallFamilyFunctional : ConeHalfBallFamilyFunctionalStep
  /-- Lemma 3.3: interior estimate. Owner: m1. -/
  greenKernelInterior : GreenKernelInteriorStep 𝒮
  /-- Lemma 3.3: boundary estimate. PROVED (`greenKernelBoundaryStep`, m1) but not importable together with Lemma 3.7
  (F12: `MatedCRT.harmonicAt_comp_add_const` is declared by m1 and by x1). Owner: m1/x1 (rename). -/
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
  /-- Propositions 4.2 and 5.1: the least supersolution is strictly above the obstacle on the harmonic ball
  (eq:strictly-above-in-interior; E-x3-1, E-c2-5). Replaces `ObstacleClusterInnerApproximationStep`
  (`obstacleClusterInnerApproximation_of_strictGap`). Owner: x3. -/
  harmonicBallStrictObstacleGap : HarmonicBallStrictObstacleGapStep 𝒮
  /-- Lemma 4.6 (corrected route): local compactness of the odometers. Owner: x3. -/
  odometerLocalCompactnessCorrected : OdometerLocalCompactnessCorrectedStep 𝒮
  /-- Lemma 4.6 (corrected route): boundary upgrade. Owner: x3. -/
  odometerBoundaryUpgradeCorrected : OdometerBoundaryUpgradeCorrectedStep 𝒮
  /-- Lemma 4.6: measurable selection of the subsequence (E-x3-2). Owner: x3. -/
  odometerMeasurableSelection : OdometerMeasurableSelectionStep 𝒮
  /-- Lemma 4.8 (corrected route): distributional limit of the Laplacians. PROVED
  (`odometerDistributionalLimitCorrectedStep_of_greenKernel`, x3, 7582c60) but not importable together with Lemma 3.3
  (F15: `MatedCRT.rescaledGreenKernel` is declared in Steps/Sec3/UniformConvergenceGreenKernel.lean and in
  Proofs/Sec4/SubsequentialProperties/ClusterContainment.lean). Owner: x3 (rename). -/
  odometerDistributionalLimitCorrected : OdometerDistributionalLimitCorrectedStep 𝒮
  /-- Proposition 5.1: Lemma 5.3 on `V^ε(Λ_t)` (E-c1-5, not in the paper). Owner: unassigned. -/
  stoppedMeanValueInequality : StoppedMeanValueInequalityStep 𝒮
  /-- Proposition 5.1: Lemma 5.4 on `V^ε(Λ_t)` (E-c1-5, not in the paper). Owner: unassigned. -/
  stoppedLLowerBound : StoppedLLowerBoundStep 𝒮
  /-- Lemma 5.3 (through `meanValueSurplusStep_of_lower`): the lower surplus estimate (E-x1-1). Owner: x1. -/
  meanValueSurplusLower : MeanValueSurplusLowerStep 𝒮
  /-- Lemma 6.4: restriction of the cone field to annuli has mean zero (IR-c4-5). Owner: c2. -/
  coneMeanZeroRestriction : ConeMeanZeroRestrictionStep
  /-- Lemma 6.4: circle averages modulo constants (locality of the good annulus events, IR-c4-6). Owner: c2. -/
  circleAverageModConst : CircleAverageModConstStep
  /-- Lemma 6.5: existence of the whole-plane LQG objects (IR-c4-1). Owner: c2. -/
  wholePlaneLQGExistence : WholePlaneLQGExistenceStep
  /-- Lemma 6.5: Weyl comparison of the cone and whole-plane fields (IR-c4-2). Owner: c2. -/
  coneWholePlaneWeylComparison : ConeWholePlaneWeylComparisonStep
  /-- Lemma 6.5: coordinate change (IR-c4-3). Owner: c2. -/
  wholePlaneLQGCoordinateChange : WholePlaneLQGCoordinateChangeStep
  /-- Lemma 6.5: upper volume tail of the whole-plane LQG measure (IR-c4-4). Owner: c2. -/
  wholePlaneUpperVolumeTail : WholePlaneUpperVolumeTailStep
  -- (d) Awaiting an operator ruling
  /-- **Lemma 3.1**, Draft form (E-c1-4: false for closed `D`, by a written argument; review-L32 N1, N3). Consumed
  only by Lemma 3.3 (m1); Lemmas 3.5 and 4.6 use the corrected form, Lemma 3.7 the almost-sure corrected form. -/
  discretePotentialTightness : DiscretePotentialTightnessStmt 𝒮
  /-- The corrected cited **Lemma 3.2** (GMS19 Theorem 3.9; review-L32 "minimal corrected statement", ruling (L2)
  pending; the Draft 3.2 is false by review-L32 F1). Used by the corrected Lemma 3.1. -/
  discreteHolderContinuityCorrected : DiscreteHolderContinuityCorrectedStep 𝒮
  /-- **Lemma 3.1**, corrected interior form with almost-sure hypotheses (E-c2-6: the `∀ ω` hypotheses of the frozen
  3.1 cannot be met by a `σ(h, η)`-measurable `u^ε` against `S.mult`). Used by Lemma 3.7
  (`convergenceNormalizedExitTime_of_statements`). -/
  discretePotentialTightnessAe : DiscretePotentialTightnessAeStep 𝒮
  -- (e) Paper-owned results with no committed reduction
  /-- **Lemma 3.4** (convergence of integrals of the Green function). Owner: m2. Used by 3.3, 3.5. -/
  integralConvergenceGreenFunction : IntegralConvergenceGreenFunctionStmt 𝒮

end MatedCRT
