import MatedCRT
import MatedCRT.Steps.Sec2.ConeHarmonicBalls
import MatedCRT.Steps.Sec2.MaximumPrinciple
import MatedCRT.Steps.Sec2.BoundedExitTimeRV
import MatedCRT.Steps.Sec2.ExpectedExitTimeExplicitBound
import MatedCRT.Steps.Sec4.ConvergenceDivisible
import MatedCRT.Steps.Sec4.DivSandpileLowerBound
import MatedCRT.Steps.Sec4.SubsequentialConvergence
import MatedCRT.Steps.Sec4.SubsequentialProperties
import MatedCRT.Steps.Sec4.ObstacleSpecialization
import MatedCRT.Proofs.Sec4.ObstacleSpecialization
import MatedCRT.Proofs.Sec4.Equibounded
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.OdometerComparison
import MatedCRT.Steps.Sec5.GeneralIDLALowerBound
import MatedCRT.Proofs.Sec5.GeneralIDLALowerBound.Statement
import MatedCRT.Proofs.Sec5.GeneralIDLALowerBound.CellCount
import MatedCRT.Steps.Sec5.MeanValueInequality
import MatedCRT.Steps.Sec5.LLowerBound
import MatedCRT.Proofs.Sec5.LLowerBound.GreenSum
import MatedCRT.Proofs.Sec5.IDLALowerBound.Statement
import MatedCRT.Proofs.Sec6.AbelianIDLA.Statement
import MatedCRT.Steps.Sec6.GoodAnnulusPrevalence
import MatedCRT.Steps.Sec6.AnnulusHit
import MatedCRT.Steps.Sec6.AnnulusIterate
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Statement
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.OfSteps
import MatedCRT.Proofs.Sec6.ChanceOfBeingAbsorbed.Statement
import MatedCRT.Proofs.Sec6.IterativeBound.Statement
import MatedCRT.Steps.Sec7.MassBoundOdometer
import MatedCRT.Steps.Sec7.OdometerBoundMass
import MatedCRT.Steps.Sec7.CrudeUpperBound
import MatedCRT.Proofs.SecA.Statements
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.MaximumPrinciple
import MatedCRT.Proofs.Field.LawTransferComplete
import MatedCRT.Proofs.Sec6.GoodAnnulusPrevalence.ConeTransfer
import MatedCRT.Steps.Sec3.DiscretePotentialTightness
import MatedCRT.Steps.Sec3.DiscreteDirichletProblem
import MatedCRT.Steps.Sec3.ConvergenceHarmonicFunctions
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.OfInteriorBoundary
import MatedCRT.Proofs.Sec5.LLowerBound.OfEvents
import MatedCRT.Proofs.Sec5.MeanValueInequality.NormalizedStep
import MatedCRT.Proofs.Sec6.IDLAUpperBound.OfSteps
import MatedCRT.Steps.Sec8.IDLAConstrainedConvergence
import MatedCRT.Steps.Sec1.Convergence
import MatedCRT.Steps.Sec2.ConeHarmonicBallsUpToFixedTime
import MatedCRT.Proofs.Sec2.LQGMeasureProperties.Locality
import MatedCRT.Audit.CorrectedForms
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Final
import MatedCRT.Proofs.Sec6.AnnulusHit.Main
import MatedCRT.Proofs.Sec6.GoodAnnulusPrevalence.Main
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Main
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ConeScalingPositivity
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.OdometerComparisonProved
import MatedCRT.Proofs.Sec5.LLowerBound.OfInputs
import MatedCRT.Proofs.Measurability.EnvSigma
import MatedCRT.Proofs.Sec6.GoodAnnulusPrevalence.Locality
import MatedCRT.Proofs.Sec1.Main
import MatedCRT.Proofs.Sec1.EnvironmentScaling
import MatedCRT.Proofs.Sec2.Final
import MatedCRT.Proofs.Sec2.LQGMeasureProperties.NonAtomicScaling
import MatedCRT.Proofs.Sec2.VolumeGrowthHalf.Main
import MatedCRT.Proofs.Sec2.CellSizeHalf.Main
import MatedCRT.Proofs.Measurability.LQGMeasureField
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Final
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.AlmostSureInterior
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.DyadicModulus
import MatedCRT.Proofs.Sec4.ObstacleSpecialization.Final
import MatedCRT.Proofs.Sec4.SubsequentialConvergence.Corrected
import MatedCRT.Proofs.Sec4.SubsequentialProperties.Final
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.Final
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.Final
import MatedCRT.Proofs.Sec5.IDLALowerBound.Final
import MatedCRT.Proofs.Sec5.MeanValueInequality.SurplusSteps
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Final
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ShellIterationOfMeshScaling
import MatedCRT.Proofs.Field.ConeCircleModConst

/-!
# Audit: the current reductions of the numbered results

For every numbered result of "Internal DLA on mated-CRT maps" (arXiv:2211.04891) whose reduction is committed, an
`example` restates the best current reduction with its exact hypothesis list: the Draft statements of other numbered
results (`...Stmt`, `MatedCRT/Draft`), the literature inputs (`...Input`, `MatedCRT/External`) and the open step
Props (`...Step`, `MatedCRT/Steps`). Every proved step is discharged inside the example (this includes `AdjacentCellsMeetAeStep`, proved by `adjacentCellsMeetAeStep`). If a Draft statement, a
reduction theorem or a step changes, or a reduction acquires a new hypothesis, this file stops compiling. The summary
table, with the reducing theorems' locations, is `docs/campaign/REDUCTIONS.md`.

Each example closes its goal with `audit_apply e` (`apply e`, then `assumption` on every hypothesis of `e`), so the
binders of the example are exactly the hypotheses the reduction still needs.

Where a Draft statement is false or open (for Lemma 4.4, Lemma 7.2, Lemma 6.9 and Lemmas 6.4-6.10), the example names the corrected statement that is proved (`...CorrectedStmt`,
`...AboveScaleStmt`, `...LocalRateStmt`, `...LogStmt`), and the docstring records which consumers still use the
Draft form.

Leonardo Bonanno's code (lean-formalizations, ported to `LatticeProb.Bonanno` in Lattice-Probability) enters through
the imported modules: the mated-CRT map of Definition 1.1 (`bmEdgeCount`, `LatticeProb.Bonanno.MatedCRTHarmonic`, via
`MatedCRT.Defs.Map`; `AdjacentCellsMeetAeStep` from his mating-of-trees bundle, via
`MatedCRT.Proofs.MatingOfTrees.AdjacentCells`) and Lemma 6.6 (`LQGMetric.LM.lmLem3_1a`,
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`, via `MatedCRT.Proofs.Field.LawTransferComplete`).
-/

/-- `audit_apply e`: apply the reduction theorem `e` and close each of its hypotheses by a hypothesis of the
`example`; a new hypothesis of `e` makes the example fail. -/
macro "audit_apply " e:term : tactic => `(tactic| (apply $e <;> assumption))

namespace MatedCRT.Audit

/-! ## Section 1 and Proposition 8.1 -/

/-- **Theorem 1.4** from Proposition 8.1 and four scaling steps (`convergenceOfIDLA_of_steps`). -/
example (𝒮 : SpaceFillingSLEModel) (h81 : IDLAConstrainedConvergenceStmt 𝒮) (h1 : ConeEnvironmentScalingStep 𝒮)
    (h2 : HarmonicBallFamilyScalingStep) (h3 : ConeScaleRadiusStep) (h4 : ScaledClusterExitTimeStep) :
    ConvergenceOfIDLAStmt 𝒮 := by
  audit_apply convergenceOfIDLA_of_steps

/-- **Theorem 1.6** from Proposition 8.1 and four scaling steps (`convergenceOfDivSandpile_of_steps`). -/
example (𝒮 : SpaceFillingSLEModel) (h81 : IDLAConstrainedConvergenceStmt 𝒮) (h1 : ConeEnvironmentScalingStep 𝒮)
    (h2 : HarmonicBallFamilyScalingStep) (h3 : ConeScaleRadiusStep) (h4 : ScaledClusterExitTimeStep) :
    ConvergenceOfDivSandpileStmt 𝒮 := by
  audit_apply convergenceOfDivSandpile_of_steps

/-- **Proposition 8.1** from Propositions 4.2, 5.1, Theorem 6.1 and Proposition 7.1
(`iDLAConstrainedConvergence_of_steps`, annealed union bounds; no step). -/
example (𝒮 : SpaceFillingSLEModel) (h42 : DivSandpileLowerBoundStmt 𝒮) (h51 : IDLALowerBoundStmt 𝒮)
    (h61 : IDLAUpperBoundStmt 𝒮) (h71 : DivSandpileUpperBoundStmt 𝒮) : IDLAConstrainedConvergenceStmt 𝒮 := by
  audit_apply iDLAConstrainedConvergence_of_steps

/-! ## Section 2 -/

/-- **Theorem 2.3** from Lemmas 2.4, 2.5 and `ConeFamilyAEMeasurableStep` (`coneHarmonicBalls_of_steps`). -/
example (h24 : ConeHarmonicBallsUpToFixedTimeStmt) (h25 : ConeScaleInvarianceUpToFixedTimeStmt)
    (hfam : ConeFamilyAEMeasurableStep) : ConeHarmonicBallsStmt := by
  audit_apply coneHarmonicBalls_of_steps

/-- **Lemma 2.4** from six cone and whole-plane harmonic-ball steps (`coneHarmonicBallsUpToFixedTime_of_steps`). -/
example (h1 : WholePlaneLogLQGExistenceStep) (h2 : WholePlaneConeHarmonicBallsStep)
    (h3 : WholePlaneHarmonicBallsSmallTimeStep) (h4 : ConeRestrictionStep) (h5 : ConeHarmonicBallLocalityStep)
    (h6 : ConeHarmonicBallStrictGrowthStep) : ConeHarmonicBallsUpToFixedTimeStmt := by
  audit_apply coneHarmonicBallsUpToFixedTime_of_steps

/-! **Lemmas 2.5 and 2.6** (`coneScaleInvarianceUpToFixedTime_of_steps`, MatedCRT/Steps/Sec2/ConeScaleInvarianceUpTo
FixedTime.lean:260; `coneScaleInvariance_of_steps`, MatedCRT/Steps/Sec2/ConeScaleInvariance.lean:104) are checked only in docs/campaign/REDUCTIONS.md: `MatedCRT.rescaledMeasure` is declared both in MatedCRT.Steps.Sec1.Convergence and in
the Lemma 2.5 module chain, so Theorems 1.4/1.6 and Lemmas 2.5/2.6
cannot be imported together. Once one is renamed, restore the imports and these examples (hypothesis lists):

    example (hQ : QuantumConeScalingInput) (h1 : ConeHarmonicBallStrictGrowthStep) (h2 : ConeLQGScalingStep)
        (h3 : ConeRescaledCircleAEMeasurableStep) (h4 : ConeHalfBallFamilyFunctionalStep)
        (h5 : ConeHarmonicBallFamilyOnScalingStep) : ConeScaleInvarianceUpToFixedTimeStmt := by
      audit_apply coneScaleInvarianceUpToFixedTime_of_steps

    example (hQ : QuantumConeScalingInput) (h1 : ConeLQGScalingStep) (h2 : ConeRescaledCircleAEMeasurableStep)
        (h3 : ConeHarmonicBallFunctionalStep) (h4 : ConeHarmonicBallFamilyOnScalingStep) :
        ConeScaleInvarianceStmt := by
      audit_apply coneScaleInvariance_of_steps

the input-level forms (MatedCRT/Proofs/Sec2/ConeScaleInvarianceUpToFixedTime/Main.lean:21, 30, 61 and
MatedCRT/Proofs/Sec2/ConeScaleInvariance/Main.lean:14; `ConeHarmonicBallFamilyOnScalingStep` proved, `ConeLQGScaling
Step` from Fact 2.2 and `ConeScaleRadiusPosStep`), equally blocked by F10, hypothesis lists:
Lemma 2.5 `coneScaleInvarianceUpToFixedTime_of_inputs` (QuantumConeScalingInput, LQGMeasurePropertiesStmt,
ConeScaleRadiusPosStep, ConeHarmonicBallStrictGrowthStep, ConeRescaledCircleAEMeasurableStep,
ConeHalfBallFamilyFunctionalStep); Lemma 2.6 `coneScaleInvariance_of_inputs` (QuantumConeScalingInput,
LQGMeasurePropertiesStmt, ConeScaleRadiusPosStep, ConeRescaledCircleAEMeasurableStep, ConeHarmonicBallFunctionalStep);
Theorem 2.3 `coneHarmonicBalls_of_inputs` (the six steps of Lemma 2.4 and the inputs of Lemma 2.5; A's
`ConeFamilyAEMeasurableStep` derived by `coneFamilyAEMeasurableStep_of_steps`).
-/

/-- **Fact 2.2** (cited) from its cited parts (DS11): non-atomicity and dilation covariance, and the locality step
`ConeCircleAverageLocalityStep` (`LQGMeasure.lqgMeasureProperties_of_steps`). The part Props are not in
MatedCRT/External. -/
example (hna : LQGMeasureNonAtomicPart) (hloc : ConeCircleAverageLocalityStep)
    (hdil : LQGMeasureDilationCovariancePart) : LQGMeasurePropertiesStmt := by
  audit_apply LQGMeasure.lqgMeasureProperties_of_steps

/-- **Lemma 2.13**, proved: `maximumPrinciple_of_steps` with `AdjacentCellsMeetAeStep` proved
(`adjacentCellsMeetAeStep`, on Leonardo Bonanno's mating-of-trees bundle). -/
example (𝒮 : SpaceFillingSLEModel) : MaximumPrincipleStmt 𝒮 := by
  have hadj : AdjacentCellsMeetAeStep 𝒮 := adjacentCellsMeetAeStep 𝒮
  audit_apply maximumPrinciple_of_steps

/-- **Lemma 2.17** from Lemma 2.7 (`boundedExitTimeRV_of_steps`). -/
example (h27 : VolumeGrowthStmt) : BoundedExitTimeRVStmt := by
  audit_apply boundedExitTimeRV_of_steps

/-- **Lemma 2.19** from Lemmas 2.7 and 2.18 (`expectedExitTimeExplicitBound_of_steps`, through Lemma 2.17). -/
example (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) (h218 : ExitTimeUpperBoundStmt 𝒮) :
    ExpectedExitTimeExplicitBoundStmt 𝒮 := by
  have h217 : BoundedExitTimeRVStmt := by audit_apply boundedExitTimeRV_of_steps
  audit_apply expectedExitTimeExplicitBound_of_steps

/-! ## Section 3 -/

/-- **Lemma 3.1**, corrected form `DiscretePotentialTightnessCorrectedStmt` (`D` open; [C6] Hölder data `C'ε⁻¹`, [C11] polynomially summable scales), from two steps (`discretePotentialTightness_of_steps`). The Draft
`DiscretePotentialTightnessStmt` (false for non-open `D`) has no reduction; Lemmas 3.3, 3.7 and 4.6 consume
it. -/
example (𝒮 : SpaceFillingSLEModel) (heq : TightnessEquicontinuityStep 𝒮) (hsel : TightnessSelectionStep 𝒮) :
    DiscretePotentialTightnessCorrectedStmt 𝒮 := by
  audit_apply discretePotentialTightness_of_steps

/-- **Lemma 3.1**, corrected form, from Lemmas 2.17, 2.18, the literature input `MepsScalingInput` and the corrected
Lemma 3.2 `DiscreteHolderContinuityCorrectedStep` (`DiscreteHolderContinuityCorrectedStep`)
(`discretePotentialTightness_of_inputs`; both steps of the previous example proved). -/
example (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮) (h217 : BoundedExitTimeRVStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h32 : DiscreteHolderContinuityCorrectedStep 𝒮) :
    DiscretePotentialTightnessCorrectedStmt 𝒮 := by
  have hadj : AdjacentCellsMeetAeStep 𝒮 := adjacentCellsMeetAeStep 𝒮
  audit_apply discretePotentialTightness_of_inputs

/-! **Lemma 3.3** from Lemmas 2.10, 3.4, 2.14, 2.8, 3.1 (Draft), 2.13 and two steps
(`uniformConvergenceGreenKernel_of_steps`). The boundary step is proved (`greenKernelBoundaryStep`,
MatedCRT/Proofs/Sec3/UniformConvergenceGreenKernel/BoundaryStep.lean:16, with `uniformConvergenceGreenKernel_of_interior
Step` :131 needing `GreenKernelInteriorStep` only), but that module cannot be imported together with Lemma 3.7's:
`MatedCRT.harmonicAt_comp_add_const` is declared both in Proofs/Sec3/UniformConvergenceGreenKernel/HarmonicTranslation
and in a Proofs/Sec3/ConvergenceNormalizedExitTime module. Once renamed, switch to:

    example (𝒮 : SpaceFillingSLEModel) (h210 : DegreeMeasureConvergenceStmt 𝒮)
        (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
        (h28 : CellSizeEstimateStmt 𝒮) (h31 : DiscretePotentialTightnessStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
        (hi : GreenKernelInteriorStep 𝒮) : UniformConvergenceGreenKernelStmt 𝒮 := by
      audit_apply uniformConvergenceGreenKernel_of_interiorStep

DISABLED: the module of this reduction, MatedCRT/Steps/Sec3/
UniformConvergenceGreenKernel.lean, declares `MatedCRT.rescaledGreenKernel` (:16), which is also declared in
MatedCRT/Proofs/Sec4/SubsequentialProperties/ClusterContainment.lean:26, imported by the final forms of Lemma 4.8 and
Theorem 4.1 (section `FinalForms`). Lemma 3.3 cannot be imported together with them. The example was:

    example (𝒮 : SpaceFillingSLEModel) (h210 : DegreeMeasureConvergenceStmt 𝒮)
        (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
        (h28 : CellSizeEstimateStmt 𝒮) (h31 : DiscretePotentialTightnessStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
        (hi : GreenKernelInteriorStep 𝒮) (hb : GreenKernelBoundaryStep 𝒮) : UniformConvergenceGreenKernelStmt 𝒮 := by
      audit_apply uniformConvergenceGreenKernel_of_steps
-/

/-- **Lemma 3.5** from the cited Hölder estimate for Green potentials (`HarmonicBalls.GreenPotentialHolderStmt`),
Lemmas 3.6, 3.4, 3.1 (corrected), 2.13, 2.19, 2.8 and three steps (`discreteDirichletProblem_of_steps`). -/
example (𝒮 : SpaceFillingSLEModel) (hGP : HarmonicBalls.GreenPotentialHolderStmt.{0})
    (h36 : ConvergenceHarmonicFunctionsStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h31 : DiscretePotentialTightnessCorrectedStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
    (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮) (hl : DirichletLimitStep 𝒮)
    (hi : DirichletInteriorStep 𝒮) (hb : DirichletBoundaryStep 𝒮) : DiscreteDirichletProblemStmt 𝒮 := by
  audit_apply discreteDirichletProblem_of_steps

/-- **Lemma 3.6** from Lemmas 2.11, 2.8 and two steps (`convergenceHarmonicFunctions_of_steps`). -/
example (𝒮 : SpaceFillingSLEModel) (h211 : RandomWalkToLBMStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hp : HarmonicPathExitStep 𝒮) (hc : HarmonicExitCellStep 𝒮) : ConvergenceHarmonicFunctionsStmt 𝒮 := by
  audit_apply convergenceHarmonicFunctions_of_steps

/-- **Lemma 3.7** from Lemmas 3.3, 2.9, 2.19, 3.5, 3.1 (Draft), 2.8, 2.17 and two steps
(`convergenceNormalizedExitTime_of_interior_discrete_boundary`). -/
example (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮) (h31 : DiscretePotentialTightnessStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h217 : BoundedExitTimeRVStmt) (hi : NormalizedExitInteriorStep 𝒮)
    (hb : DiscreteExitBoundaryStep 𝒮) : ConvergenceNormalizedExitTimeStmt 𝒮 := by
  audit_apply convergenceNormalizedExitTime_of_interior_discrete_boundary

/-! ## Section 4 -/

/-- **Theorem 4.1** from Lemmas 4.6, 4.8 and `ConvergenceDivisibleEventMeasurableStep` (`convergenceDivisible_of_steps`;
the uniqueness step proved by `obstacleLimitUniqueness`, from the proved steps `matedCRTScalingConstantPositive`
and `obstacleLimitMaximumPrinciple`). -/
example (𝒮 : SpaceFillingSLEModel) (h48 : SubsequentialPropertiesStmt 𝒮) (h46 : SubsequentialConvergenceStmt 𝒮)
    (hmeas : ConvergenceDivisibleEventMeasurableStep 𝒮) : ConvergenceDivisibleStmt 𝒮 := by
  have huniq : ObstacleLimitUniquenessStep 𝒮 := obstacleLimitUniqueness 𝒮
  audit_apply convergenceDivisible_of_steps

/-- **Theorem 4.1** from Lemmas 4.6, 4.8, 2.7 and `ConeEnvironmentScalingStep` (the scaling step of Theorems 1.4,
1.6) (`convergenceDivisible_of_scaling`: the event-measurability step from the cone scaling). -/
example (𝒮 : SpaceFillingSLEModel) (h48 : SubsequentialPropertiesStmt 𝒮) (h46 : SubsequentialConvergenceStmt 𝒮)
    (h27 : VolumeGrowthStmt) (hsc : ConeEnvironmentScalingStep 𝒮) : ConvergenceDivisibleStmt 𝒮 := by
  audit_apply convergenceDivisible_of_scaling

/-- **Proposition 4.2** from Theorems 4.1, 2.3, Lemmas 2.13, 3.3, 2.8 and `ObstacleClusterInnerApproximationStep`
(`divSandpileLowerBound_of_inputs`; the odometer comparison proved by `divSandpileOdometerComparison`). -/
example (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮) (h23 : ConeHarmonicBallsStmt)
    (h213 : MaximumPrincipleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hin : ObstacleClusterInnerApproximationStep 𝒮) : DivSandpileLowerBoundStmt 𝒮 := by
  audit_apply divSandpileLowerBound_of_inputs

/-- **Lemma 4.3** from `BallInteriorConnectedStep` (`discreteBasicProperties_of_inputs`). -/
example (𝒮 : SpaceFillingSLEModel) (hconn : BallInteriorConnectedStep 𝒮) : DiscreteBasicPropertiesStmt 𝒮 := by
  have hadj : AdjacentCellsMeetAeStep 𝒮 := adjacentCellsMeetAeStep 𝒮
  have hG : GreenKernelLaplacianStep := greenKernelLaplacianStep
  have hN : NormExitTimeLaplacianStep := normExitTimeLaplacianStep
  audit_apply discreteBasicProperties_of_inputs

/-- **Lemma 4.4**, corrected form, from `BallInteriorConnectedStep`
(`discreteLaplacianBoundCorrected_of_inputs`). The Draft `DiscreteLaplacianBoundStmt` (false;
`CorrectedForms.not_discreteLaplacianBoundStmt`) has no reduction; Lemmas 4.6 and 4.8 still consume it (7.2-7.4 are
checked below through this corrected form). -/
example (𝒮 : SpaceFillingSLEModel) (hconn : BallInteriorConnectedStep 𝒮) :
    DiscreteLaplacianBoundCorrectedStmt 𝒮 := by
  have hadj : AdjacentCellsMeetAeStep 𝒮 := adjacentCellsMeetAeStep 𝒮
  have hG : GreenKernelLaplacianStep := greenKernelLaplacianStep
  audit_apply discreteLaplacianBoundCorrected_of_inputs

/-- **Lemma 4.5**, corrected form, from `BallInteriorConnectedStep`
(`discreteConservationOfMassCorrected_of_inputs`). -/
example (𝒮 : SpaceFillingSLEModel) (hconn : BallInteriorConnectedStep 𝒮) :
    DiscreteConservationOfMassCorrectedStmt 𝒮 := by
  have hadj : AdjacentCellsMeetAeStep 𝒮 := adjacentCellsMeetAeStep 𝒮
  have hG : GreenKernelLaplacianStep := greenKernelLaplacianStep
  audit_apply discreteConservationOfMassCorrected_of_inputs

/-- **Lemma 4.6** from Lemmas 4.7, 4.4 (Draft), 3.1, 3.5 and three steps
(`subsequentialConvergence_of_steps`). -/
example (𝒮 : SpaceFillingSLEModel) (h47 : EquiboundedStmt 𝒮) (h44 : DiscreteLaplacianBoundStmt 𝒮)
    (h31 : DiscretePotentialTightnessStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (hc : OdometerLocalCompactnessStep 𝒮) (hb : OdometerBoundaryUpgradeStep 𝒮)
    (hs : OdometerMeasurableSelectionStep 𝒮) : SubsequentialConvergenceStmt 𝒮 := by
  audit_apply subsequentialConvergence_of_steps

/-- **Lemma 4.7** from Lemmas 4.3, 2.17, 2.18 and the literature input `MepsScalingInput` (`equibounded_of_steps`). -/
example (𝒮 : SpaceFillingSLEModel) (h43 : DiscreteBasicPropertiesStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hm : MepsScalingInput 𝒮) : EquiboundedStmt 𝒮 := by
  audit_apply equibounded_of_steps

/-- **Lemma 4.8** from Lemmas 3.3, 3.5, 3.7, 4.6, 4.3, 4.4 (Draft), 2.13 and two steps
(`subsequentialProperties_of_steps`). -/
example (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮) (h37 : ConvergenceNormalizedExitTimeStmt 𝒮)
    (h46 : SubsequentialConvergenceStmt 𝒮) (h43 : DiscreteBasicPropertiesStmt 𝒮)
    (h44 : DiscreteLaplacianBoundStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
    (happ : OdometerObstacleApproximationStep 𝒮) (hlim : OdometerDistributionalLimitStep 𝒮) :
    SubsequentialPropertiesStmt 𝒮 := by
  audit_apply subsequentialProperties_of_steps

/-! ## Section 5 -/

/-- **Proposition 5.1** from Lemmas 2.7, 2.8, 5.3, 5.4, Theorems 4.1, 2.3, Lemmas 2.13, 3.3 and two steps
(`iDLALowerBound_of_volumeGrowth_cellSize`: `EnvSigmaMeasurableStep` no longer needed, `σ(h, η)` is
null-measurable; the discrete-cluster form of Proposition 4.2 from `discreteClusterInnerBound_of_steps`). -/
example (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h53 : MeanValueInequalityStmt 𝒮) (h54 : LLowerBoundStmt 𝒮) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h213 : MaximumPrincipleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (hin : ObstacleClusterInnerApproximationStep 𝒮) (hstop : IDLALowerBoundStoppedStep 𝒮) :
    IDLALowerBoundStmt 𝒮 := by
  have hI : DiscreteClusterInnerBoundStep 𝒮 := by audit_apply discreteClusterInnerBound_of_steps
  audit_apply iDLALowerBound_of_volumeGrowth_cellSize

/-- **Lemma 5.2** from the cited Lemmas 2.7, 2.8 only (`generalIDLALowerBound_of_volumeGrowth_cellSize`). -/
example (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮) :
    GeneralIDLALowerBoundStmt 𝒮 := by
  audit_apply generalIDLALowerBound_of_volumeGrowth_cellSize

/-- **Lemma 5.3** from Lemmas 4.4 (corrected), 2.13, 4.1, 3.3, 2.18 and `MeanValueSurplusStep`
(`meanValueInequality_of_surplus`). -/
example (𝒮 : SpaceFillingSLEModel) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hsur : MeanValueSurplusStep 𝒮) : MeanValueInequalityStmt 𝒮 := by
  audit_apply meanValueInequality_of_surplus

/-- **Lemma 5.4** from the cited Lemmas 2.15, 2.16, 2.9 only (`lLowerBound_of_inputs`). -/
example (𝒮 : SpaceFillingSLEModel) (h215 : GreenFunctionCrudeBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) : LLowerBoundStmt 𝒮 := by
  audit_apply lLowerBound_of_inputs

/-! ## Section 6 -/

/-- **Lemma 6.3**, proved (`AbelianIDLA.abelianIDLA`). -/
example (𝒮 : SpaceFillingSLEModel) : AbelianIDLAStmt 𝒮 := AbelianIDLA.abelianIDLA 𝒮

/-- **Lemma 6.4** from Lemma 6.5 and two field steps (`goodAnnulusPrevalence_of_annulusHit`; Lemma 6.6 proved, from `ConeMeanZeroRestrictionStep` by `annulusIterateConeTransfer`, from `CircleAverageModConstStep` by
`goodAnnulusEventLocality`). -/
example (h65 : AnnulusHitStmt) (hR : ConeMeanZeroRestrictionStep) (hD : CircleAverageModConstStep) :
    GoodAnnulusPrevalenceStmt := by
  audit_apply goodAnnulusPrevalence_of_annulusHit

/-- **Lemma 6.5** from four whole-plane field steps (`annulusHit_of_volumeTail`; the tightness step from the GMC
volume tail by `wholePlaneGoodAnnulusTightness_of_volumeTail`). -/
example (h1 : WholePlaneLQGExistenceStep) (h2 : ConeWholePlaneWeylComparisonStep)
    (h3 : WholePlaneLQGCoordinateChangeStep) (h4 : WholePlaneUpperVolumeTailStep) : AnnulusHitStmt := by
  audit_apply annulusHit_of_volumeTail

/-- **Lemma 6.6**, proved (`annulusIterate`: `annulusIterate_of_leo` on Leonardo Bonanno's
`LQGMetric.LM.lmLem3_1a`, with the law transfer `annulusGFFLawTransfer : AnnulusGFFLawTransferStep`). -/
example : AnnulusIterateStmt := annulusIterate

/-- **Lemma 6.7** from Lemmas 6.8 (Draft, no log loss), 2.7, 2.8, 2.19 (`constantOrderLowerBound`). -/
example (𝒮 : SpaceFillingSLEModel) (h68 : ConstantOrderLowerBoundDivStmt 𝒮) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮) :
    ConstantOrderLowerBoundStmt 𝒮 := by
  have hadj : AdjacentCellsMeetAeStep 𝒮 := adjacentCellsMeetAeStep 𝒮
  audit_apply constantOrderLowerBound

/-- **Lemma 6.8**, [C5] log-loss form `ConstantOrderLowerBoundDivLogStmt` (`1 - s₂/(1+|log r|)²`), from Lemmas 2.16,
2.7, 2.8, 2.9, 2.18, 6.4 and `LQGMeasureFieldMeasurableStep` (`constantOrderLowerBoundDiv_of_inputs`: the
false-as-drafted `GoodScaleEventMeasurableStep` replaced by its a.s. form, proved from
`LQGMeasureFieldMeasurableStep`). The Draft `ConstantOrderLowerBoundDivStmt` has no reduction; Lemma 6.7 (Draft
form), 6.9 (local rate) and Proposition 7.1 consume it. -/
example (𝒮 : SpaceFillingSLEModel) (h216 : GreenKernelLowerBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (h29 : CountingMeasureConvergenceStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h64 : GoodAnnulusPrevalenceStmt) (hμ : LQGMeasureFieldMeasurableStep 𝒮) :
    ConstantOrderLowerBoundDivLogStmt 𝒮 := by
  audit_apply constantOrderLowerBoundDiv_of_inputs

/-- **Lemma 6.9**, local-rate form `ChanceOfBeingAbsorbedLocalRateStmt`, from Lemma 6.7
(`chanceOfBeingAbsorbedLocalRate`). The Draft `ChanceOfBeingAbsorbedStmt` implies it
(`ChanceOfBeingAbsorbedStmt.localRate`) but has no reduction. -/
example (𝒮 : SpaceFillingSLEModel) (h67 : ConstantOrderLowerBoundStmt 𝒮) :
    ChanceOfBeingAbsorbedLocalRateStmt 𝒮 := by
  audit_apply chanceOfBeingAbsorbedLocalRate

/-- **Lemma 6.7**, [C5] log-loss form `ConstantOrderLowerBoundLogStmt` (absorption probability `s₂/(1+|log r|)²`), from
Lemmas 6.8 ([C5] form), 2.7, 2.8, 2.19 (`constantOrderLowerBoundLog`). -/
example (𝒮 : SpaceFillingSLEModel) (h68 : ConstantOrderLowerBoundDivLogStmt 𝒮) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮) :
    ConstantOrderLowerBoundLogStmt 𝒮 := by
  have hadj : AdjacentCellsMeetAeStep 𝒮 := adjacentCellsMeetAeStep 𝒮
  audit_apply constantOrderLowerBoundLog

/-- **Lemma 6.9**, [C5] log-loss form `ChanceOfBeingAbsorbedLogLossStmt` (with `s₃` chosen after `s₀`), from
Lemma 6.7 ([C5] form) (`chanceOfBeingAbsorbedLogLoss_of_steps`, the Chernoff step proved). -/
example (𝒮 : SpaceFillingSLEModel) (h67 : ConstantOrderLowerBoundLogStmt 𝒮) :
    ChanceOfBeingAbsorbedLogLossStmt 𝒮 := by
  have hC : AbsorptionChernoffStep := Absorption.absorptionChernoffStep
  audit_apply chanceOfBeingAbsorbedLogLoss_of_steps

/-- **Lemma 6.10** from Lemmas 6.8 ([C5] form), 2.7, 2.8, 2.19, through Lemmas 6.7 and 6.9 ([C5] forms) (`iterativeBound_of_div`;
`AdjacentCellsMeetStep` from `AdjacentCellsMeetAeStep.probTendsToOne`). -/
example (𝒮 : SpaceFillingSLEModel) (h68 : ConstantOrderLowerBoundDivLogStmt 𝒮) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮) : IterativeBoundStmt 𝒮 := by
  have hadj : AdjacentCellsMeetAeStep 𝒮 := adjacentCellsMeetAeStep 𝒮
  audit_apply iterativeBound_of_div

/-- **Theorem 6.1** from Lemma 6.10, Proposition 5.1 and `BoundaryLayerMeasurableStep`
(`IDLAUpperBound.iDLAUpperBound_of_steps`; Lemma 6.3 used in its proved form). -/
example (𝒮 : SpaceFillingSLEModel) (h610 : IterativeBoundStmt 𝒮) (h51 : IDLALowerBoundStmt 𝒮)
    (hm : BoundaryLayerMeasurableStep 𝒮) (hfam : ConeFamilyAEMeasurableStep)
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt) : IDLAUpperBoundStmt 𝒮 := by
  audit_apply IDLAUpperBound.iDLAUpperBound_of_steps

/-! ## Section 7 -/

/-! **Proposition 7.1**: the final form (`divSandpileUpperBound_of_meshScaling`, no Draft 7.2) is checked in the
section `FinalForms` below. The earlier carved form (`divSandpileUpperBound_of_carved_inputs`,
MatedCRT/Steps/Sec7/DivSandpileUpperBound.lean:164) had the hypothesis list:

    example (𝒮 : SpaceFillingSLEModel) (h23 : ConeHarmonicBallsStmt) (h68 : ConstantOrderLowerBoundDivStmt 𝒮)
        (h27 : VolumeGrowthStmt) (h72 : MassBoundOdometerStmt 𝒮) (h41 : ConvergenceDivisibleStmt 𝒮)
        (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
        (h73 : OdometerBoundMassStmt 𝒮) (h74 : CrudeUpperBoundStmt 𝒮)
        (hset : StoppedObstacleSetupStep 𝒮) (hconf : StoppedShellConfinementStep 𝒮) :
        DivSandpileUpperBoundStmt 𝒮 := by
      audit_apply divSandpileUpperBound_of_carved_inputs

It consumes the Draft 7.2 `MassBoundOdometerStmt`, refuted ([C8]), and the Draft 6.8 (no log loss, [C5]), so it
is vacuous until it is rerouted through `MassBoundOdometerAboveScaleStmt` and `ConstantOrderLowerBoundDivLogStmt`. -/

/-- **Lemma 7.2**, corrected form `MassBoundOdometerAboveScaleStmt` ([C8], `s ≥ ε^β`), from Lemmas 2.16, 2.8 and
the corrected Lemma 4.4 (`CorrectedForms.massBoundOdometerAboveScale_of_corrected`, in place of the false Draft 4.4 used by `massBoundOdometerAboveScale_of_draft`). -/
example (𝒮 : SpaceFillingSLEModel) (h216 : GreenKernelLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮) : MassBoundOdometerAboveScaleStmt 𝒮 := by
  audit_apply CorrectedForms.massBoundOdometerAboveScale_of_corrected

/-- **Lemma 7.3** from the corrected Lemma 4.4 (`CorrectedForms.odometerBoundMass_of_corrected`). -/
example (𝒮 : SpaceFillingSLEModel) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮) : OdometerBoundMassStmt 𝒮 := by
  audit_apply CorrectedForms.odometerBoundMass_of_corrected

/-- **Lemma 7.4** from the corrected Lemma 4.4 and the literature input `DegreeBoundInput`
(`CorrectedForms.crudeUpperBound_of_corrected`). -/
example (𝒮 : SpaceFillingSLEModel) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮) (hdeg : DegreeBoundInput 𝒮) :
    CrudeUpperBoundStmt 𝒮 := by
  audit_apply CorrectedForms.crudeUpperBound_of_corrected

/-! ## Appendix A: proved -/

/-- **Lemma A.1**, proved. -/
example : DiscreteDivergenceTheoremStmt := discreteDivergenceTheorem

/-- **Lemma A.2**, proved. -/
example : DiscreteBasicPropertiesGeneralStmt := discreteBasicPropertiesGeneral

/-- **Lemma A.3**, proved. -/
example : DiscreteLaplacianBoundGeneralStmt := discreteLaplacianBoundGeneral

/-- **Lemma A.4**, proved. -/
example : DiscreteConservationOfMassGeneralStmt := discreteConservationOfMassGeneral

/-! ## Final forms

The reduction of each result (theorem ⇒ statement, with its hypothesis
list). The examples above record earlier reductions that still compile. Proved statements and steps are discharged:
Lemmas 2.13, 4.3, corrected 4.4, corrected 4.5 (`discreteBasicProperties`, `discreteLaplacianBoundCorrected`,
`discreteConservationOfMassCorrected`), `LQGMeasureFieldMeasurableStep`, `OdometerObstacleApproximationStep`,
`OdometerDistributionalLimitCorrectedStep` (from Lemma 3.3). -/

section FinalForms

/-- **Theorem 1.4**, final form: Propositions 4.2, 5.1, 6.1, 7.1 and Fact 2.2, the literature inputs
`QuantumConeScalingInput`, the three SLE inputs, the steps `RescaledConeFieldStep`, `RescaledConeClockStep`,
`RescaledMatingOfTreesStep`, and the Section 2 steps `ConeHarmonicBallStrictGrowthStep`,
`ConeHalfBallFamilyFunctionalStep` (`convergenceOfIDLA_of_bounds_coneSteps` with
`coneEnvironmentScalingStep_of_inputs`). -/
example (𝒮 : SpaceFillingSLEModel) (h42 : DivSandpileLowerBoundStmt 𝒮) (h51 : IDLALowerBoundStmt 𝒮)
    (h61 : IDLAUpperBoundStmt 𝒮) (h71 : DivSandpileUpperBoundStmt 𝒮) (h22 : LQGMeasurePropertiesStmt)
    (hscale : QuantumConeScalingInput) (hsi : SLEScaleInvarianceInput 𝒮) (hrp : SLEReparametrizationInput 𝒮)
    (him : SLEIndepMonoInput 𝒮) (hfield : RescaledConeFieldStep 𝒮) (hclock : RescaledConeClockStep 𝒮)
    (hmating : RescaledMatingOfTreesStep 𝒮) (hgrow : ConeHarmonicBallStrictGrowthStep)
    (hfun : ConeHalfBallFamilyFunctionalStep) : ConvergenceOfIDLAStmt 𝒮 := by
  have henv : ConeEnvironmentScalingStep 𝒮 := by audit_apply coneEnvironmentScalingStep_of_inputs
  audit_apply convergenceOfIDLA_of_bounds_coneSteps

/-- **Theorem 1.6**, final form: as Theorem 1.4 (`convergenceOfDivSandpile_of_bounds_coneSteps`). -/
example (𝒮 : SpaceFillingSLEModel) (h42 : DivSandpileLowerBoundStmt 𝒮) (h51 : IDLALowerBoundStmt 𝒮)
    (h61 : IDLAUpperBoundStmt 𝒮) (h71 : DivSandpileUpperBoundStmt 𝒮) (h22 : LQGMeasurePropertiesStmt)
    (hscale : QuantumConeScalingInput) (hsi : SLEScaleInvarianceInput 𝒮) (hrp : SLEReparametrizationInput 𝒮)
    (him : SLEIndepMonoInput 𝒮) (hfield : RescaledConeFieldStep 𝒮) (hclock : RescaledConeClockStep 𝒮)
    (hmating : RescaledMatingOfTreesStep 𝒮) (hgrow : ConeHarmonicBallStrictGrowthStep)
    (hfun : ConeHalfBallFamilyFunctionalStep) : ConvergenceOfDivSandpileStmt 𝒮 := by
  have henv : ConeEnvironmentScalingStep 𝒮 := by audit_apply coneEnvironmentScalingStep_of_inputs
  audit_apply convergenceOfDivSandpile_of_bounds_coneSteps

/-- **Fact 2.2**, final form: Lemma 2.7, the cited non-dyadic dilation covariance (DS11; a Part outside
MatedCRT/External, F11), the quantum cone scaling input and the steps `ConeCircleAverageLocalityStep`,
`ConeFieldScalingStep` (`LQGMeasure.lqgMeasureProperties_of_volumeGrowth`). -/
example (h27 : VolumeGrowthStmt) (hnd : LQGMeasureNonDyadicDilationPart) (hloc : ConeCircleAverageLocalityStep)
    (hfs : LQGMeasure.ConeFieldScalingStep) (hscale : QuantumConeScalingInput) : LQGMeasurePropertiesStmt := by
  have hpos : ConeScaleRadiusPosStep := coneScaleRadiusPosStep_of_input hscale
  audit_apply LQGMeasure.lqgMeasureProperties_of_volumeGrowth

/-- **Measurability of the stopped cone families** (`ConeFamilyAEMeasurableStep`, a step of 2.3, 4.1, 4.2, 5.1, 6.1):
from Lemma 2.7, strict growth, the quantum cone scaling and the three parts of Fact 2.2
(`coneFamilyAEMeasurable_final`). -/
example (h27 : VolumeGrowthStmt) (hgrow : ConeHarmonicBallStrictGrowthStep) (hscale : QuantumConeScalingInput)
    (hna : LQGMeasureNonAtomicPart) (hloc : LQGMeasureLocalityPart) (hdil : LQGMeasureDilationCovariancePart) :
    ConeFamilyAEMeasurableStep := by
  audit_apply coneFamilyAEMeasurable_final

/-- **Theorem 2.3**, final form (`coneHarmonicBalls_final`): the harmonic-balls Draft statements, five Section 2
steps, the quantum cone scaling input, the three parts of Fact 2.2 and Lemma 2.7. -/
example (hHB : HarmonicBallsDraftInputs) (h0 : WholePlaneLogLQGExistenceStep) (h3 : ConeRestrictionStep)
    (h4 : ConeHarmonicBallLocalityStep) (hgrow : ConeHarmonicBallStrictGrowthStep) (hscale : QuantumConeScalingInput)
    (hna : LQGMeasureNonAtomicPart) (hloc : LQGMeasureLocalityPart) (hdil : LQGMeasureDilationCovariancePart)
    (h27 : VolumeGrowthStmt) (hfun : ConeHalfBallFamilyFunctionalStep) : ConeHarmonicBallsStmt := by
  audit_apply coneHarmonicBalls_final

/-- **Lemma 2.4**, final form (`coneHarmonicBallsUpToFixedTime_final`). -/
example (hHB : HarmonicBallsDraftInputs) (h0 : WholePlaneLogLQGExistenceStep) (h3 : ConeRestrictionStep)
    (h4 : ConeHarmonicBallLocalityStep) (hgrow : ConeHarmonicBallStrictGrowthStep) :
    ConeHarmonicBallsUpToFixedTimeStmt := by
  audit_apply coneHarmonicBallsUpToFixedTime_final

/-- **Lemma 2.5**, final form (`coneScaleInvarianceUpToFixedTime_final`). -/
example (hgrow : ConeHarmonicBallStrictGrowthStep) (hscale : QuantumConeScalingInput)
    (hna : LQGMeasureNonAtomicPart) (hloc : LQGMeasureLocalityPart) (hdil : LQGMeasureDilationCovariancePart)
    (hfun : ConeHalfBallFamilyFunctionalStep) : ConeScaleInvarianceUpToFixedTimeStmt := by
  audit_apply coneScaleInvarianceUpToFixedTime_final

/-- **Lemma 2.6**, final form (`coneScaleInvariance_final`; its law equality). -/
example (hscale : QuantumConeScalingInput) (hna : LQGMeasureNonAtomicPart) (hloc : LQGMeasureLocalityPart)
    (hdil : LQGMeasureDilationCovariancePart) (hfun : ConeHarmonicBallFunctionalStep) : ConeScaleInvarianceStmt := by
  audit_apply coneScaleInvariance_final

/-- **Lemma 2.7, lower half** (Leonardo Bonanno's whole-plane comparison): from `ConeWholePlaneCouplingStep`. -/
example (hc : ConeWholePlaneCouplingStep) : VolumeGrowthLowerStmt := by
  audit_apply volumeGrowthLowerStmt_of_coupling

/-- **Lemma 2.8, upper half**: from `ConeWholePlaneCouplingStep`. -/
example (𝒮 : SpaceFillingSLEModel) (hc : ConeWholePlaneCouplingStep) : CellSizeUpperStmt 𝒮 := by
  audit_apply cellSizeUpperStmt_of_coupling

/-- **Lemma 3.1**, corrected form, final: Lemmas 2.7, 2.18, `MepsScalingInput` and the corrected cited
Lemma 3.2 ([C6]) (`discretePotentialTightnessCorrected_of_inputs`). -/
example (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮) (h27 : VolumeGrowthStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h32 : DiscreteHolderContinuityCorrectedStep 𝒮) :
    DiscretePotentialTightnessCorrectedStmt 𝒮 := by
  audit_apply discretePotentialTightnessCorrected_of_inputs

/-- The almost-sure interior form of Lemma 3.1 follows from the same inputs. -/
example (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮) (h27 : VolumeGrowthStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h32 : DiscreteHolderContinuityCorrectedStep 𝒮) :
    DiscretePotentialTightnessAeStep 𝒮 :=
  discretePotentialTightnessAeStep_of_inputs hm (boundedExitTimeRV_of_steps h27) h218 h32

/-- **Lemma 3.7**, final form: Lemmas 3.3, 3.5, 2.17, 2.18 and the a.s. interior form of the corrected 3.1
(`DiscretePotentialTightnessAeStep`) (`convergenceNormalizedExitTime_of_statements`). -/
example (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h218 : ExitTimeUpperBoundStmt 𝒮) (hAe : DiscretePotentialTightnessAeStep 𝒮) :
    ConvergenceNormalizedExitTimeStmt 𝒮 := by
  audit_apply convergenceNormalizedExitTime_of_statements

/-- **Theorem 4.1**, final form (`convergenceDivisible_final_of_coneFamily`): Lemmas 2.7, 2.18, 3.3, 3.5, 3.7,
2.4, `MepsScalingInput`, the corrected cited Lemma 3.2, `ConeFamilyAEMeasurableStep` (derived above) and three
odometer steps of Lemma 4.6. -/
example (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) (h218 : ExitTimeUpperBoundStmt 𝒮) (hm : MepsScalingInput 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h37 : ConvergenceNormalizedExitTimeStmt 𝒮) (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (hfam : ConeFamilyAEMeasurableStep) (h32 : DiscreteHolderContinuityCorrectedStep 𝒮)
    (hlc : OdometerLocalCompactnessCorrectedStep 𝒮) (hbu : OdometerBoundaryUpgradeCorrectedStep 𝒮)
    (hsel : OdometerMeasurableSelectionStep 𝒮) : ConvergenceDivisibleStmt 𝒮 := by
  audit_apply convergenceDivisible_final_of_coneFamily

/-- **Proposition 4.2**, final form (`divSandpileLowerBound_final`): Theorem 4.1, 2.3, Lemmas 2.4, 2.7,
2.8, 3.3, `ConeFamilyAEMeasurableStep` and the strict obstacle gap `HarmonicBallStrictObstacleGapStep`. -/
example (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮) (h23 : ConeHarmonicBallsStmt)
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (hfam : ConeFamilyAEMeasurableStep)
    (hgap : HarmonicBallStrictObstacleGapStep 𝒮) : DivSandpileLowerBoundStmt 𝒮 := by
  audit_apply divSandpileLowerBound_final

/-- **Lemma 4.3**, proved. -/
example (𝒮 : SpaceFillingSLEModel) : DiscreteBasicPropertiesStmt 𝒮 := discreteBasicProperties 𝒮

/-- **Lemma 4.4**, corrected form, proved. -/
example (𝒮 : SpaceFillingSLEModel) : DiscreteLaplacianBoundCorrectedStmt 𝒮 := discreteLaplacianBoundCorrected 𝒮

/-- **Lemma 4.5**, corrected form, proved. -/
example (𝒮 : SpaceFillingSLEModel) : DiscreteConservationOfMassCorrectedStmt 𝒮 :=
  discreteConservationOfMassCorrected 𝒮

/-- **Lemma 4.6**, final form (`subsequentialConvergence_of_inputs`; no Draft 3.1, no Draft 4.4): `MepsScalingInput`,
Lemmas 2.7, 2.18, 3.5, the corrected cited Lemma 3.2 and three odometer steps. -/
example (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮) (h27 : VolumeGrowthStmt) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h32 : DiscreteHolderContinuityCorrectedStep 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (hlc : OdometerLocalCompactnessCorrectedStep 𝒮) (hbu : OdometerBoundaryUpgradeCorrectedStep 𝒮)
    (hsel : OdometerMeasurableSelectionStep 𝒮) : SubsequentialConvergenceStmt 𝒮 := by
  audit_apply subsequentialConvergence_of_inputs

/-- **Lemma 4.7**, final form: Lemmas 2.7, 2.18 and `MepsScalingInput` (`equibounded_of_inputs`). -/
example (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hm : MepsScalingInput 𝒮) : EquiboundedStmt 𝒮 := by
  audit_apply equibounded_of_inputs

/-- **Lemma 4.8**, final form: Lemmas 3.3, 3.5, 3.7; Lemma 2.13 proved; no step
(`subsequentialProperties_of_inputs`, with `OdometerDistributionalLimitCorrectedStep` proved from Lemma 3.3). -/
example (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h37 : ConvergenceNormalizedExitTimeStmt 𝒮) : SubsequentialPropertiesStmt 𝒮 := by
  have hadj : AdjacentCellsMeetAeStep 𝒮 := adjacentCellsMeetAeStep 𝒮
  have h213 : MaximumPrincipleStmt 𝒮 := by audit_apply maximumPrinciple_of_steps
  audit_apply subsequentialProperties_of_inputs

/-- **Proposition 5.1**, final form (`iDLALowerBound_final_of_strictGap`): cited Lemmas 2.7, 2.8, 2.9, 2.15,
2.16, 2.18; Theorem 4.1, 2.3, Lemmas 2.4, 3.3, 2.17; `ConeFamilyAEMeasurableStep`; the surplus lower bound of Lemma
5.3, the strict obstacle gap and the stopped forms of Lemmas 5.3, 5.4. -/
example (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h215 : GreenFunctionCrudeBoundStmt 𝒮)
    (h216 : GreenKernelLowerBoundStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h217 : BoundedExitTimeRVStmt) (hfam : ConeFamilyAEMeasurableStep)
    (hsur : MeanValueSurplusLowerStep 𝒮) (hgap : HarmonicBallStrictObstacleGapStep 𝒮)
    (hsm : StoppedMeanValueInequalityStep 𝒮) (hsl : StoppedLLowerBoundStep 𝒮) : IDLALowerBoundStmt 𝒮 := by
  have h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮 := discreteLaplacianBoundCorrected 𝒮
  have hfm : LQGMeasureFieldMeasurableStep 𝒮 := LQGMeasureField.lqgMeasureFieldMeasurableStep 𝒮
  audit_apply iDLALowerBound_final_of_strictGap

/-- **Lemma 5.3**, final form (`meanValueInequality_of_lower`): Theorem 4.1, Lemmas 3.3, 2.17, 2.18 and the surplus
lower bound `MeanValueSurplusLowerStep`; corrected 4.4, 2.13 and the field measurability proved. -/
example (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt) (hsur : MeanValueSurplusLowerStep 𝒮) :
    MeanValueInequalityStmt 𝒮 := by
  have h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮 := discreteLaplacianBoundCorrected 𝒮
  have hadj : AdjacentCellsMeetAeStep 𝒮 := adjacentCellsMeetAeStep 𝒮
  have h213 : MaximumPrincipleStmt 𝒮 := by audit_apply maximumPrinciple_of_steps
  have hfm : LQGMeasureFieldMeasurableStep 𝒮 := LQGMeasureField.lqgMeasureFieldMeasurableStep 𝒮
  audit_apply meanValueInequality_of_lower

/-- **Theorem 6.1**, final form (`iDLAUpperBound_final`): Lemma 6.10, Proposition 5.1 and the Section 2
inputs of Lemma 2.4 and of `ConeFamilyAEMeasurableStep`. -/
example (𝒮 : SpaceFillingSLEModel) (h610 : IterativeBoundStmt 𝒮) (h51 : IDLALowerBoundStmt 𝒮)
    (hHB : HarmonicBallsDraftInputs) (h0 : WholePlaneLogLQGExistenceStep) (h3 : ConeRestrictionStep)
    (h4 : ConeHarmonicBallLocalityStep) (hgrow : ConeHarmonicBallStrictGrowthStep) (hscale : QuantumConeScalingInput)
    (hna : LQGMeasureNonAtomicPart) (hloc : LQGMeasureLocalityPart) (hdil : LQGMeasureDilationCovariancePart)
    (h27 : VolumeGrowthStmt) : IDLAUpperBoundStmt 𝒮 := by
  audit_apply iDLAUpperBound_final

/-- **Lemma 6.4**, final form (`goodAnnulusPrevalence_final`): five whole-plane/cone field steps;
`CircleAverageModConstStep` is proved (`Field.ConeCircle.circleAverageModConstStep`). -/
example (h1 : WholePlaneLQGExistenceStep) (h2 : ConeWholePlaneWeylComparisonStep)
    (h3 : WholePlaneLQGCoordinateChangeStep) (h4 : WholePlaneUpperVolumeTailStep) (hR : ConeMeanZeroRestrictionStep) :
    GoodAnnulusPrevalenceStmt := by
  have hD : CircleAverageModConstStep := Field.ConeCircle.circleAverageModConstStep
  audit_apply goodAnnulusPrevalence_final

/-- The field hypotheses shared by the final forms of Lemmas 6.7 (b)-6.10 (`..._final`,
Proofs/Sec6/ConstantOrderLowerBoundDiv/Final.lean): cited 2.7, 2.8, 2.9, 2.16, 2.18 and the five open field steps of
6.4; `LQGMeasureFieldMeasurableStep` and `CircleAverageModConstStep` are proved. -/
example (𝒮 : SpaceFillingSLEModel) (h216 : GreenKernelLowerBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (h29 : CountingMeasureConvergenceStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h1 : WholePlaneLQGExistenceStep) (h2 : ConeWholePlaneWeylComparisonStep)
    (h3 : WholePlaneLQGCoordinateChangeStep) (h4 : WholePlaneUpperVolumeTailStep) (hR : ConeMeanZeroRestrictionStep) :
    ConstantOrderLowerBoundLogStmt 𝒮 ∧ ConstantOrderLowerBoundDivLogStmt 𝒮 ∧ ChanceOfBeingAbsorbedLogLossStmt 𝒮 ∧
      IterativeBoundStmt 𝒮 := by
  have hfm : LQGMeasureFieldMeasurableStep 𝒮 := LQGMeasureField.lqgMeasureFieldMeasurableStep 𝒮
  have hD : CircleAverageModConstStep := Field.ConeCircle.circleAverageModConstStep
  refine ⟨?_, ?_, ?_, ?_⟩
  · audit_apply constantOrderLowerBoundLog_final
  · audit_apply constantOrderLowerBoundDivLog_final
  · audit_apply chanceOfBeingAbsorbedLogLoss_final
  · audit_apply iterativeBound_final

/-- **Proposition 7.1**, final form (`divSandpileUpperBound_of_meshScaling`; no step, no Draft 7.2, no Draft
6.8): `MepsScalingInput`, Theorems 2.3, 4.1, Lemmas 6.8 ([C5] form), 2.7, corrected 7.2, 3.3, 2.8, 7.3, 7.4. -/
example (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮) (h23 : ConeHarmonicBallsStmt)
    (h68 : ConstantOrderLowerBoundDivLogStmt 𝒮) (h27 : VolumeGrowthStmt) (h72 : MassBoundOdometerAboveScaleStmt 𝒮)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h73 : OdometerBoundMassStmt 𝒮) (h74 : CrudeUpperBoundStmt 𝒮) : DivSandpileUpperBoundStmt 𝒮 := by
  audit_apply divSandpileUpperBound_of_meshScaling

/-- **Lemmas 7.2 (corrected), 7.3, 7.4**, final forms: the corrected Lemma 4.4 is proved. -/
example (𝒮 : SpaceFillingSLEModel) (h216 : GreenKernelLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hdeg : DegreeBoundInput 𝒮) :
    MassBoundOdometerAboveScaleStmt 𝒮 ∧ OdometerBoundMassStmt 𝒮 ∧ CrudeUpperBoundStmt 𝒮 := by
  have h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮 := discreteLaplacianBoundCorrected 𝒮
  refine ⟨?_, ?_, ?_⟩
  · audit_apply CorrectedForms.massBoundOdometerAboveScale_of_corrected
  · audit_apply CorrectedForms.odometerBoundMass_of_corrected
  · audit_apply CorrectedForms.crudeUpperBound_of_corrected

end FinalForms

end MatedCRT.Audit
