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
import MatedCRT.Proofs.Sec5.StoppedSurplusSteps
import MatedCRT.Proofs.Sec5.StoppedExterior
import MatedCRT.Proofs.Sec5.StoppedInterior

/-!
# The remaining hypotheses of Theorems 1.4 and 1.6

`MainHypotheses 𝒮` collects, one field per Prop, every hypothesis that the committed reductions of the numbered results
of "Internal DLA on mated-CRT maps" (Bou-Rabee and Gwynne, arXiv:2211.04891) still need in order to give Theorems 1.4
and 1.6 (`convergenceOfIDLA_conditional`, `convergenceOfDivSandpile_conditional`, MatedCRT/Assembly/Main.lean). A
proved step or a proved numbered result is not a field: it is discharged in Main.lean. A field is also dropped when its
Prop is reduced to fields already present, or to admitted inputs: `DirichletLimitStep` is discharged this way, by
`dirichletLimitStep_of_volumeGrowth` from `volumeGrowth` (2026-11-07).

The fields are grouped:
* (a) cited results of the paper (Draft statements of results the paper quotes from the literature), and the
  statements of [BG22] the paper cites, from the harmonic-balls formalization;
* (b) literature inputs (`...Input`, MatedCRT/External);
* (c) open named steps (`...Step`), with their owner (task files of 2026-11-07; "no current owner" when no task file
  names the step);
* (d) statements awaiting an operator ruling: a corrected cited statement whose admission is pending, and a corrected
  form of a frozen statement;
* (e) paper-owned numbered results whose committed reduction still needs open steps that are not fields.

No field is a Draft statement refuted in Lean (MatedCRT/Audit/Main.lean checks this against MatedCRT/Audit/*, among
them the Draft Lemmas 4.4, 4.5 (Audit/CorrectedForms.lean) and the Draft Lemma 3.1 (Audit/Refutations.lean)).
This file is regenerated as steps close: a field disappears when its Prop is proved or reduced.
-/

namespace MatedCRT

/-- The remaining hypotheses of the conditional proof of Theorems 1.4 and 1.6 for the space-filling SLE model `𝒮`.
Field counts (regenerated 2026-11-07): (a) 12, (b) 3, (c) 23, (d) 2, (e) 1; total 41.

No field is a Draft known false: the Draft Lemma 3.1 (refuted in Lean, `not_discretePotentialTightnessStmt`, E-c1-4)
is no longer consumed, since Lemma 3.3 goes through the almost-sure corrected 3.1 (`uniformConvergenceGreenKernel_final`,
763b7d7). The Draft Lemmas 4.4 and 4.5 (refuted in Lean, Audit/CorrectedForms.lean) are used only in their corrected
forms. -/
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
  `RescaledEnvironmentInput` (IR-c1-1). Owner: m5 (task cone-environment-scaling); the admission of
  `RescaledEnvironmentInput` is for the operator. -/
  coneEnvironmentScaling : ConeEnvironmentScalingStep 𝒮
  /-- Lemma 2.4: existence of the whole-plane log-singular LQG objects. Owner: c5 (sec2-finalize). -/
  wholePlaneLogLQGExistence : WholePlaneLogLQGExistenceStep
  /-- Lemma 2.4: restriction to the cone. Owner: c5. -/
  coneRestriction : ConeRestrictionStep
  /-- Lemma 2.4: locality of the cone harmonic balls. Owner: c5. -/
  coneHarmonicBallLocality : ConeHarmonicBallLocalityStep
  /-- Lemmas 2.4, 2.5, Theorems 1.4, 1.6: strict growth of the cone harmonic balls (`T' = T`, E-c5-3, not in the
  paper). Owner: c5 / operator (E-c5-3: admit as an External input?). -/
  coneHarmonicBallStrictGrowth : ConeHarmonicBallStrictGrowthStep
  /-- Lemma 2.5, Theorems 1.4, 1.6: the half-ball family is a functional of the field. Owner: c5. -/
  coneHalfBallFamilyFunctional : ConeHalfBallFamilyFunctionalStep
  /-- Lemma 3.5: interior estimate. Reduced (`dirichletInteriorStep_of_moduli`) to `DirichletPointwiseStep` and
  `DirichletDiscreteModulusStep`, which are open and not fields. Owner: c1 (task brownian-dirichlet-disc). -/
  dirichletInterior : DirichletInteriorStep 𝒮
  /-- Lemma 3.5: boundary estimate. Owner: c1 (task brownian-dirichlet-disc). -/
  dirichletBoundary : DirichletBoundaryStep 𝒮
  /-- Lemma 3.6: planar Brownian motion makes an outward excursion right after its exit from a disk (strong Markov
  property at the exit time and Blumenthal's 0-1 law, Mörters-Peres Thms 2.16, 2.7; not in MarkovProcess). Used by
  `convergenceHarmonicFunctions_of_inputs` (ab6ed20). Owner: m2 (task sec3-lbm-steps) / operator (input request: strong
  Markov, 0-1 law). -/
  brownianOutwardExcursionAtExit : BrownianOutwardExcursionAtExitStep
  /-- Lemma 3.6: measurability of bounded Lipschitz functionals of rescaled Liouville Brownian motion (joint
  measurability of the LQG clock). Used by `convergenceHarmonicFunctions_of_inputs`. Owner: m2. -/
  lbmPathFunctionalMeasurable : LBMPathFunctionalMeasurableStep 𝒮
  /-- Propositions 4.2 and 5.1: the least supersolution is strictly above the obstacle on the harmonic ball
  (eq:strictly-above-in-interior; E-x3-1, E-c2-5). Replaces `ObstacleClusterInnerApproximationStep`
  (`obstacleClusterInnerApproximation_of_strictGap`). Owner: m6 (task m6-prop42-strict-obstacle-gap). -/
  harmonicBallStrictObstacleGap : HarmonicBallStrictObstacleGapStep 𝒮
  /-- Lemma 4.6 (corrected route): local compactness of the odometers. No current owner (x3.md assigned Lemma 4.6 to
  c1; no current task file names the step). -/
  odometerLocalCompactnessCorrected : OdometerLocalCompactnessCorrectedStep 𝒮
  /-- Lemma 4.6 (corrected route): boundary upgrade. No current owner (as above). -/
  odometerBoundaryUpgradeCorrected : OdometerBoundaryUpgradeCorrectedStep 𝒮
  /-- Lemma 4.6: measurable selection of the subsequence (E-x3-2). No current owner (as above). -/
  odometerMeasurableSelection : OdometerMeasurableSelectionStep 𝒮
  /-- Proposition 5.1: Lemma 5.3 on `V^ε(Λ_t)` (E-c1-5), interior lower bound of the obstacle surplus. Not a field
  any more: `StoppedSurplusInteriorStep` is supplied by `stoppedSurplusInterior_of_gap` from the strict obstacle gap
  `harmonicBallStrictObstacleGap`, `mepsScaling` and the three named inputs below (z1, 2026-11-08; E-c1-5 (c)-(e)). -/
  stoppedSurplusPole : StoppedInterior.StoppedSurplusPoleStep 𝒮
  /-- Lemma 5.3 on `V^ε(Λ_t)` (E-c1-5 (d)): the discrete-to-continuum geometry of the `δ`-interior. -/
  stoppedInteriorGeometry : StoppedInterior.StoppedInteriorGeometryStep 𝒮
  /-- Lemma 5.3 on `V^ε(Λ_t)` (E-c1-5 (e)): measurability of the continuum margin on the random compact set. -/
  stoppedInteriorMeasurable : StoppedInterior.StoppedInteriorMeasurableStep 𝒮
  /-- Proposition 5.1: Lemma 5.3 on `V^ε(Λ_t)` (E-c1-5), exterior upper bound of the obstacle surplus. The field
  `StoppedSurplusExteriorStep` is no longer assumed: it is supplied by `stoppedSurplusExterior_of_nullMeasurableOrigin`
  from `mepsScaling` and this origin measurability input (z1, 2026-11-08; ESCALATIONS E-c1-5 (b)). -/
  coneOriginNullMeasurable : ConeOriginNullMeasurableStep 𝒮
  /-- Proposition 5.1: Lemma 5.3 on `V^ε(Λ_t)` (E-c1-5), Green potential of the boundary layer `A \ Λ^ε_t`.
  No current owner. -/
  stoppedLayerPotential : StoppedLayerPotentialStep 𝒮
  /-- Lemma 5.3 (through `meanValueSurplusStep_of_lower`): the lower surplus estimate (E-x1-1, E-c2-5). No current
  owner. -/
  meanValueSurplusLower : MeanValueSurplusLowerStep 𝒮
  /-- Lemma 6.4: restriction of the cone field to annuli has mean zero (IR-c4-5). Owner: z1 (z1-sec6-annulus-hit-finish). -/
  coneMeanZeroRestriction : ConeMeanZeroRestrictionStep
  /-- Lemma 6.5: existence of the whole-plane LQG objects (IR-c4-1). Owner: z1. -/
  wholePlaneLQGExistence : WholePlaneLQGExistenceStep
  /-- Lemma 6.5: Weyl comparison of the cone and whole-plane fields (IR-c4-2). Owner: z1. -/
  coneWholePlaneWeylComparison : ConeWholePlaneWeylComparisonStep
  /-- Lemma 6.5: coordinate change (IR-c4-3). Owner: z1. -/
  wholePlaneLQGCoordinateChange : WholePlaneLQGCoordinateChangeStep
  /-- Lemma 6.5: upper volume tail of the whole-plane LQG measure (IR-c4-4). Owner: z1. -/
  wholePlaneUpperVolumeTail : WholePlaneUpperVolumeTailStep
  -- (d) Awaiting an operator ruling
  /-- The corrected cited **Lemma 3.2** (GMS19 Theorem 3.9; review-L32 "minimal corrected statement", ruling (L2)
  pending; the Draft 3.2 is false by review-L32 F1). Used by the corrected Lemma 3.1. Owner: m1 (from Leo, per
  REDUCTIONS.md). -/
  discreteHolderContinuityCorrected : DiscreteHolderContinuityCorrectedStep 𝒮
  /-- **Lemma 3.1**, corrected interior form with almost-sure hypotheses (E-c2-6: the `∀ ω` hypotheses of the frozen
  3.1 cannot be met by a `σ(h, η)`-measurable `u^ε` against `S.mult`). Used by Lemmas 3.3
  (`uniformConvergenceGreenKernel_final`) and 3.7 (`convergenceNormalizedExitTime_of_statements`). Owner: m2. -/
  discretePotentialTightnessAe : DiscretePotentialTightnessAeStep 𝒮
  -- (e) Paper-owned results whose committed reduction still needs open steps
  /-- **Lemma 3.4** (convergence of integrals of the Green function). Owner: m2 (task sec3-lbm-steps; pieces committed:
  25d726a, 66df860, a8566fc, e1f2928). Reduced by `integralConvergenceGreenFunction_of_steps` to the open LBM steps
  (not fields). Used by 3.3, 3.5 and the Section 5 stopped steps. -/
  integralConvergenceGreenFunction : IntegralConvergenceGreenFunctionStmt 𝒮

end MatedCRT
