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
`dirichletLimitStep_of_volumeGrowth` from `volumeGrowth`.

The fields are grouped:
* (a) cited results of the paper (Draft statements of results the paper quotes from the literature), and the
  statements of [BG22] the paper cites, from the harmonic-balls formalization;
* (b) literature inputs (`...Input`, MatedCRT/External);
* (c) open named steps (`...Step`);
* (d) the corrected cited Lemma 3.2, retained as an explicit input;
* (e) paper-owned numbered results whose committed reduction still needs open steps that are not fields.

No field is a Draft statement refuted in Lean (MatedCRT/Audit/Main.lean checks this against MatedCRT/Audit/*, among
them the Draft Lemmas 4.4, 4.5 (Audit/CorrectedForms.lean) and the Draft Lemma 3.1 (Audit/Refutations.lean)).
This file is regenerated as steps close: a field disappears when its Prop is proved or reduced.
-/

namespace MatedCRT

/-- The remaining hypotheses of the conditional proof of Theorems 1.4 and 1.6 for the space-filling SLE model `𝒮`.
Field counts: (a) 12, (b) 3, (c) 25, (d) 1, (e) 1; total 42.

No field is a Draft known false: the Draft Lemma 3.1 (refuted in Lean, `not_discretePotentialTightnessStmt`; see docs/campaign/FROZEN-PROVENANCE.md)
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
  /-- Theorems 1.4, 1.6: the rescaled environment is valid (eq:scale-invariance-of-field-and-eta). Reduced
  (`coneEnvironmentScalingStep_of_inputs`) to the External SLE and quantum cone scaling inputs,
  Fact 2.2, and the steps `RescaledConeFieldStep`, `RescaledConeClockStep`, and
  `RescaledMatingOfTreesStep`. -/
  coneEnvironmentScaling : ConeEnvironmentScalingStep 𝒮
  /-- Lemma 2.4: existence of the whole-plane log-singular LQG objects. -/
  wholePlaneLogLQGExistence : WholePlaneLogLQGExistenceStep
  /-- Lemma 2.4: restriction to the cone. -/
  coneRestriction : ConeRestrictionStep
  /-- Lemma 2.4: locality of the cone harmonic balls. -/
  coneHarmonicBallLocality : ConeHarmonicBallLocalityStep
  /-- Lemmas 2.4, 2.5, Theorems 1.4, 1.6: strict growth of the cone harmonic balls (`T' = T`, not in the
  paper). -/
  coneHarmonicBallStrictGrowth : ConeHarmonicBallStrictGrowthStep
  /-- Lemma 2.5, Theorems 1.4, 1.6: the half-ball family is a functional of the field. -/
  coneHalfBallFamilyFunctional : ConeHalfBallFamilyFunctionalStep
  /-- Lemma 3.5: interior estimate. Reduced (`dirichletInteriorStep_of_moduli`) to `DirichletPointwiseStep` and
  `DirichletDiscreteModulusStep`, which are open and not fields. -/
  dirichletInterior : DirichletInteriorStep 𝒮
  /-- Lemma 3.5: boundary estimate. -/
  dirichletBoundary : DirichletBoundaryStep 𝒮
  /-- Lemma 3.6: planar Brownian motion makes an outward excursion right after its exit from a disk (strong Markov
  property at the exit time and Blumenthal's 0-1 law, Mörters-Peres Thms 2.16, 2.7; not in MarkovProcess). Used by
  `convergenceHarmonicFunctions_of_inputs`. -/
  brownianOutwardExcursionAtExit : BrownianOutwardExcursionAtExitStep
  /-- Lemma 3.6: measurability of bounded Lipschitz functionals of rescaled Liouville Brownian motion (joint
  measurability of the LQG clock). Used by `convergenceHarmonicFunctions_of_inputs`. -/
  lbmPathFunctionalMeasurable : LBMPathFunctionalMeasurableStep 𝒮
  /-- Propositions 4.2 and 5.1: the least supersolution is strictly above the obstacle on the harmonic ball
  (eq:strictly-above-in-interior). Replaces `ObstacleClusterInnerApproximationStep`
  (`obstacleClusterInnerApproximation_of_strictGap`). -/
  harmonicBallStrictObstacleGap : HarmonicBallStrictObstacleGapStep 𝒮
  /-- Lemma 4.6 (corrected route): local compactness of the odometers. -/
  odometerLocalCompactnessCorrected : OdometerLocalCompactnessCorrectedStep 𝒮
  /-- Lemma 4.6 (corrected route): boundary upgrade. -/
  odometerBoundaryUpgradeCorrected : OdometerBoundaryUpgradeCorrectedStep 𝒮
  /-- Lemma 4.6: measurable selection of the subsequence. -/
  odometerMeasurableSelection : OdometerMeasurableSelectionStep 𝒮
  /-- Proposition 5.1: Lemma 5.3 on `V^ε(Λ_t)`, interior lower bound of the obstacle surplus. Not a field: `StoppedSurplusInteriorStep` is supplied by `stoppedSurplusInterior_of_gap` from the strict obstacle gap
  `harmonicBallStrictObstacleGap`, `mepsScaling` and the three named inputs below. -/
  stoppedSurplusPole : StoppedInterior.StoppedSurplusPoleStep 𝒮
  /-- Lemma 5.3 on `V^ε(Λ_t)`: the discrete-to-continuum geometry of the `δ`-interior. -/
  stoppedInteriorGeometry : StoppedInterior.StoppedInteriorGeometryStep 𝒮
  /-- Lemma 5.3 on `V^ε(Λ_t)`: measurability of the continuum margin on the random compact set. -/
  stoppedInteriorMeasurable : StoppedInterior.StoppedInteriorMeasurableStep 𝒮
  /-- Proposition 5.1: Lemma 5.3 on `V^ε(Λ_t)`, exterior upper bound of the obstacle surplus. The field
  `StoppedSurplusExteriorStep` is not assumed: it is supplied by `stoppedSurplusExterior_of_nullMeasurableOrigin`
  from `mepsScaling` and this origin measurability input. -/
  coneOriginNullMeasurable : ConeOriginNullMeasurableStep 𝒮
  /-- Proposition 5.1: Lemma 5.3 on `V^ε(Λ_t)`, Green potential of the boundary layer `A \ Λ^ε_t`. -/
  stoppedLayerPotential : StoppedLayerPotentialStep 𝒮
  /-- Lemma 5.3 (through `meanValueSurplusStep_of_lower`): the lower surplus estimate. -/
  meanValueSurplusLower : MeanValueSurplusLowerStep 𝒮
  /-- Lemma 6.4: restriction of the cone field to annuli has mean zero -/
  coneMeanZeroRestriction : ConeMeanZeroRestrictionStep
  /-- Lemma 6.5: existence of the whole-plane LQG objects -/
  wholePlaneLQGExistence : WholePlaneLQGExistenceStep
  /-- Lemma 6.5: Weyl comparison of the cone and whole-plane fields -/
  coneWholePlaneWeylComparison : ConeWholePlaneWeylComparisonStep
  /-- Lemma 6.5: coordinate change -/
  wholePlaneLQGCoordinateChange : WholePlaneLQGCoordinateChangeStep
  /-- Lemma 6.5: upper volume tail of the whole-plane LQG measure -/
  wholePlaneUpperVolumeTail : WholePlaneUpperVolumeTailStep
  -- (d) Corrected cited statement
  /-- The corrected cited **Lemma 3.2** (GMS19 Theorem 3.9; correction [C6] of docs/campaign/CORRECTIONS.md).
  Used by both corrected forms of Lemma 3.1. -/
  discreteHolderContinuityCorrected : DiscreteHolderContinuityCorrectedStep 𝒮
  -- (e) Results of the paper whose committed reduction still needs open steps
  /-- **Lemma 3.4** (convergence of integrals of the Green function). Reduced by `integralConvergenceGreenFunction_of_steps` to the open LBM steps
  (not fields). Used by 3.3, 3.5 and the Section 5 stopped steps. -/
  integralConvergenceGreenFunction : IntegralConvergenceGreenFunctionStmt 𝒮

end MatedCRT
