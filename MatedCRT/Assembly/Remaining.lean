import MatedCRT.Assembly.Main
import MatedCRT.FirstPass.Derived.CellSizeOfConeCouplingProd
import MatedCRT.FirstPass.Derived.CountingMeasureOfCellSize
import MatedCRT.FirstPass.Derived.DegreeBoundOfLemma25Tail
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.PathFunctionalStep
import MatedCRT.FirstPass.Derived.QuantumConeScalingDerived
import MatedCRT.FirstPass.Derived.CoreExitTimeFromBG20
import MatedCRT.Proofs.Sec6.AnnulusHit.FieldWeylComparison
import MatedCRT.FirstPass.Derived.LQGMeasureInputs
import MatedCRT.FirstPass.Derived.UpperVolumeTail
import HarmonicBalls.FirstPass.Phase2.GreenPotentialHolderHolds
import MatedCRT.FirstPass.LPBridge.BrownianOutwardExcursion
import MatedCRT.FirstPass.LPBridge.ConeMeanZeroRestrictionFinal
import MatedCRT.FirstPass.Derived.EnvironmentScalingHolds
import MatedCRT.Proofs.Measurability.AnalyticUniversallyMeasurable
import MatedCRT.Proofs.Sec5.SupersolutionSectionIdentity
import MatedCRT.FirstPass.SLERef.Extended

/-!
# Theorems 1.4 and 1.6 for every model from the fields of `MainHypotheses` that are not proved

Fifteen of the 42 fields of `MainHypotheses 𝒮` are proved for every space-filling SLE model `𝒮`:

* Fact 2.2 (`lqgMeasureProperties`): `lqgMeasurePropertiesStmt_of_scaling` from the quantum cone scaling;
* Lemma 2.7 (`volumeGrowth`): `FirstPass.Derived.volumeGrowthStmt_holds`;
* Lemma 2.8 (`cellSizeEstimate`): `FirstPass.Derived.cellSizeEstimateStmt_holds`;
* Lemma 2.9 (`countingMeasureConvergence`): `countingMeasureConvergenceStmt_of_cellSize` from Lemma 2.8;
* the [BG22] Hölder continuity of Green potentials (`greenPotentialHolder`):
  `HarmonicBalls.greenPotentialHolderStmt_holds` of Harmonic-Balls-LQG;
* `DegreeBoundInput` (`degreeBound`): `degreeBoundInput_holds`;
* `QuantumConeScalingInput` (`quantumConeScaling`, Duplantier-Miller-Sheffield Proposition 4.13(i)):
  `FirstPass.Derived.quantumConeScalingInput_derived`;
* the steps of Lemma 3.6 (`brownianOutwardExcursionAtExit`, the outward excursion of planar Brownian motion after
  its exit from a disk, Mörters-Peres Theorems 2.16 and 2.7, and `lbmPathFunctionalMeasurable`):
  `frozenBrownianOutwardExcursionAtExit_holds`, `lbmPathFunctionalMeasurableStep_holds`;
* the null-measurability of the origin of Proposition 5.1 (`coneOriginNullMeasurable`):
  `ConeOriginNull.coneOriginNullMeasurableStep_of_preston` with the universal measurability of analytic sets,
  `prestonAnalyticUniversallyMeasurableStmt_holds`;
* the mean-zero restriction step of Lemma 6.4 (`coneMeanZeroRestriction`):
  `ConeMeanZeroRestriction.fpConeMeanZeroRestriction_holds`;
* the steps of Lemma 6.5 (`coneWholePlaneWeylComparison`, `wholePlaneLQGExistence`, `wholePlaneLQGCoordinateChange`,
  `wholePlaneUpperVolumeTail`): `AnnulusHitField.coneWholePlaneWeylComparison`,
  `FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`,
  `FirstPass.Derived.wholePlaneUpperVolumeTailStep_holds`.

A sixteenth field, the rescaled environment of Theorems 1.4 and 1.6 (`coneEnvironmentScaling`), holds for every model
that satisfies the SLE closure inputs (`coneEnvironmentScalingUnderSLE_of_scaling`). `RemainingHypotheses 𝒮` has these
closure inputs and the other 26 fields, with the same names and types; `RemainingHypotheses.toMainHypotheses`
supplies the sixteen, and `convergenceOfIDLA_of_remaining` and `convergenceOfDivSandpile_of_remaining` are Theorems
1.4 and 1.6 from `RemainingHypotheses 𝒮`. At the canonical model the first-pass route needs three premises only
(`MatedCRT/Assembly/Canonical.lean`).
-/

namespace MatedCRT

/-- The SLE closure inputs of the model and the fields of `MainHypotheses 𝒮` (`MatedCRT/Assembly/Hypotheses.lean`)
that are not proved for every model, with the same names and types. -/
structure RemainingHypotheses (𝒮 : SpaceFillingSLEModel) : Prop where
  -- (a) Cited results
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
  /-- The [BG22] statements on harmonic balls cited in Section 2 (harmonic-balls Drafts: Theorem 1.1, Theorem 5.5,
  Proposition 5.6, Lemmas 3.1-3.5, Propositions 5.2, 5.3, Lemma 5.8; `HarmonicBallsDraftInputs`). Used by 2.4. -/
  harmonicBallsDraftInputs : HarmonicBallsDraftInputs
  -- (b) Literature inputs
  /-- `MepsScalingInput` (External/SLE.lean): scaling of the expected exit time, used by 3.1 (corrected), 4.7, 7.1. -/
  mepsScaling : MepsScalingInput 𝒮
  -- (c) Open named steps
  /-- The SLE closure inputs of the model: scale invariance, reparametrization and independence of a smaller
  σ-algebra (`SLEModelClosureInput`). With the quantum cone scaling they give the rescaled environment of Theorems 1.4
  and 1.6 (`ConeEnvironmentScalingStep`, through `coneEnvironmentScalingUnderSLE_of_scaling`). -/
  sleModelClosure : SLEModelClosureInput 𝒮
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
  /-- Proposition 5.1: Lemma 5.3 on `V^ε(Λ_t)`, Green potential of the boundary layer `A \ Λ^ε_t`. -/
  stoppedLayerPotential : StoppedLayerPotentialStep 𝒮
  /-- Lemma 5.3 (through `meanValueSurplusStep_of_lower`): the lower surplus estimate. -/
  meanValueSurplusLower : MeanValueSurplusLowerStep 𝒮
  -- (d) Corrected cited statement
  /-- The corrected cited **Lemma 3.2** (GMS19 Theorem 3.9; correction [C6] of docs/campaign/CORRECTIONS.md).
  Used by both corrected forms of Lemma 3.1. -/
  discreteHolderContinuityCorrected : DiscreteHolderContinuityCorrectedStep 𝒮
  -- (e) Results of the paper whose committed reduction still needs open steps
  /-- **Lemma 3.4** (convergence of integrals of the Green function). Reduced by `integralConvergenceGreenFunction_of_steps` to the open LBM steps
  (not fields). Used by 3.3, 3.5 and the Section 5 stopped steps. -/
  integralConvergenceGreenFunction : IntegralConvergenceGreenFunctionStmt 𝒮

/-- `MainHypotheses 𝒮` from `RemainingHypotheses 𝒮`, with the sixteen fields proved from it supplied. -/
theorem RemainingHypotheses.toMainHypotheses {𝒮 : SpaceFillingSLEModel} (H : RemainingHypotheses 𝒮) :
    MainHypotheses 𝒮 :=
  { lqgMeasureProperties := lqgMeasurePropertiesStmt_of_scaling FirstPass.Derived.quantumConeScalingInput_derived
    volumeGrowth := FirstPass.Derived.volumeGrowthStmt_holds
    cellSizeEstimate := FirstPass.Derived.cellSizeEstimateStmt_holds 𝒮
    countingMeasureConvergence :=
      countingMeasureConvergenceStmt_of_cellSize (FirstPass.Derived.cellSizeEstimateStmt_holds 𝒮)
    degreeMeasureConvergence := H.degreeMeasureConvergence
    randomWalkToLBM := H.randomWalkToLBM
    greenKernelUpperBound := H.greenKernelUpperBound
    greenFunctionCrudeBound := H.greenFunctionCrudeBound
    greenKernelLowerBound := H.greenKernelLowerBound
    exitTimeUpperBound := H.exitTimeUpperBound
    greenPotentialHolder := _root_.HarmonicBalls.greenPotentialHolderStmt_holds.{0}
    harmonicBallsDraftInputs := H.harmonicBallsDraftInputs
    mepsScaling := H.mepsScaling
    degreeBound := degreeBoundInput_holds 𝒮
    quantumConeScaling := FirstPass.Derived.quantumConeScalingInput_derived
    coneEnvironmentScaling :=
      coneEnvironmentScalingUnderSLE_of_scaling 𝒮 FirstPass.Derived.quantumConeScalingInput_derived
        H.sleModelClosure.1 H.sleModelClosure.2.1 H.sleModelClosure.2.2
    wholePlaneLogLQGExistence := H.wholePlaneLogLQGExistence
    coneRestriction := H.coneRestriction
    coneHarmonicBallLocality := H.coneHarmonicBallLocality
    coneHarmonicBallStrictGrowth := H.coneHarmonicBallStrictGrowth
    coneHalfBallFamilyFunctional := H.coneHalfBallFamilyFunctional
    dirichletInterior := H.dirichletInterior
    dirichletBoundary := H.dirichletBoundary
    brownianOutwardExcursionAtExit := frozenBrownianOutwardExcursionAtExit_holds
    lbmPathFunctionalMeasurable := lbmPathFunctionalMeasurableStep_holds 𝒮
    harmonicBallStrictObstacleGap := H.harmonicBallStrictObstacleGap
    odometerLocalCompactnessCorrected := H.odometerLocalCompactnessCorrected
    odometerBoundaryUpgradeCorrected := H.odometerBoundaryUpgradeCorrected
    odometerMeasurableSelection := H.odometerMeasurableSelection
    stoppedSurplusPole := H.stoppedSurplusPole
    stoppedInteriorGeometry := H.stoppedInteriorGeometry
    stoppedInteriorMeasurable := H.stoppedInteriorMeasurable
    coneOriginNullMeasurable :=
      ConeOriginNull.coneOriginNullMeasurableStep_of_preston 𝒮 prestonAnalyticUniversallyMeasurableStmt_holds
    stoppedLayerPotential := H.stoppedLayerPotential
    meanValueSurplusLower := H.meanValueSurplusLower
    coneMeanZeroRestriction := ConeMeanZeroRestriction.fpConeMeanZeroRestriction_holds
    wholePlaneLQGExistence := FirstPass.Derived.wholePlaneLQGExistenceStep_holds
    coneWholePlaneWeylComparison := AnnulusHitField.coneWholePlaneWeylComparison
    wholePlaneLQGCoordinateChange := FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
    wholePlaneUpperVolumeTail := FirstPass.Derived.wholePlaneUpperVolumeTailStep_holds
    discreteHolderContinuityCorrected := H.discreteHolderContinuityCorrected
    integralConvergenceGreenFunction := H.integralConvergenceGreenFunction }

/-- **Theorem 1.4** (convergence of IDLA) for every space-filling SLE model, from `RemainingHypotheses 𝒮`. -/
theorem convergenceOfIDLA_of_remaining (𝒮 : SpaceFillingSLEModel) (H : RemainingHypotheses 𝒮) :
    ConvergenceOfIDLAStmt 𝒮 :=
  convergenceOfIDLA_conditional 𝒮 H.toMainHypotheses

/-- **Theorem 1.6** (convergence of the divisible sandpile) for every space-filling SLE model, from
`RemainingHypotheses 𝒮`. -/
theorem convergenceOfDivSandpile_of_remaining (𝒮 : SpaceFillingSLEModel) (H : RemainingHypotheses 𝒮) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  convergenceOfDivSandpile_conditional 𝒮 H.toMainHypotheses

end MatedCRT
