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
import MatedCRT.Steps.Sec3.UniformConvergenceGreenKernel
import MatedCRT.Steps.Sec3.ConvergenceHarmonicFunctions
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.OfInteriorBoundary
import MatedCRT.Proofs.Sec5.LLowerBound.OfEvents
import MatedCRT.Proofs.Sec5.MeanValueInequality.NormalizedStep
import MatedCRT.Proofs.Sec6.IDLAUpperBound.OfSteps
import MatedCRT.Steps.Sec8.IDLAConstrainedConvergence
import MatedCRT.Steps.Sec1.Convergence

/-!
# Audit: the current reductions of the numbered results

For every numbered result of "Internal DLA on mated-CRT maps" (arXiv:2211.04891) whose reduction is committed, an
`example` restates the best current reduction with its exact hypothesis list: the Draft statements of other numbered
results (`...Stmt`, `MatedCRT/Draft`), the literature inputs (`...Input`, `MatedCRT/External`) and the open step
Props (`...Step`, `MatedCRT/Steps`). Every proved step is discharged inside the example (since 2026-11-04 14:50Z this
includes `AdjacentCellsMeetAeStep`, proved by `adjacentCellsMeetAeStep`). If a Draft statement, a
reduction theorem or a step changes, or a reduction acquires a new hypothesis, this file stops compiling. The summary
table, with the reducing theorems' locations and owners, is `docs/campaign/REDUCTIONS.md`.

Each example closes its goal with `audit_apply e` (`apply e`, then `assumption` on every hypothesis of `e`), so the
binders of the example are exactly the hypotheses the reduction still needs.

Where a Draft statement is false or open (E-c1-1 for Lemma 4.4, E-c3-2 for Lemma 7.2, E-c5-1 for Lemma 6.9, E-A10
for Lemmas 6.4-6.10), the example names the corrected statement that is proved (`...CorrectedStmt`,
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

/-- **Lemma 2.13**, proved: `maximumPrinciple_of_steps` with `AdjacentCellsMeetAeStep` proved
(`adjacentCellsMeetAeStep`, x4, on Leonardo Bonanno's mating-of-trees bundle). -/
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

/-- **Lemma 3.1**, corrected form `DiscretePotentialTightnessCorrectedStmt` (E-c1-4 `D` open; review-L32 N1 Hölder
data `C'ε⁻¹`, N3 polynomially summable scales), from two steps (`discretePotentialTightness_of_steps`). The Draft
`DiscretePotentialTightnessStmt` (false for non-open `D`, E-c1-4) has no reduction; Lemmas 3.3 and 3.7 consume it. -/
example (𝒮 : SpaceFillingSLEModel) (heq : TightnessEquicontinuityStep 𝒮) (hsel : TightnessSelectionStep 𝒮) :
    DiscretePotentialTightnessCorrectedStmt 𝒮 := by
  audit_apply discretePotentialTightness_of_steps

/-- **Lemma 3.3** from Lemmas 2.10, 3.4, 2.14, 2.8, 3.1 (Draft, E-c1-4), 2.13 and two steps
(`uniformConvergenceGreenKernel_of_steps`). -/
example (𝒮 : SpaceFillingSLEModel) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h31 : DiscretePotentialTightnessStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
    (hi : GreenKernelInteriorStep 𝒮) (hb : GreenKernelBoundaryStep 𝒮) : UniformConvergenceGreenKernelStmt 𝒮 := by
  audit_apply uniformConvergenceGreenKernel_of_steps

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

/-- **Lemma 3.7** from Lemmas 3.3, 2.9, 2.19, 3.5, 3.1 (Draft, E-c1-4), 2.8, 2.17 and two steps
(`convergenceNormalizedExitTime_of_interior_discrete_boundary`). -/
example (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮) (h31 : DiscretePotentialTightnessStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h217 : BoundedExitTimeRVStmt) (hi : NormalizedExitInteriorStep 𝒮)
    (hb : DiscreteExitBoundaryStep 𝒮) : ConvergenceNormalizedExitTimeStmt 𝒮 := by
  audit_apply convergenceNormalizedExitTime_of_interior_discrete_boundary

/-! ## Section 4 -/

/-- **Theorem 4.1** from Lemmas 4.6, 4.8 and `ConvergenceDivisibleEventMeasurableStep` (`convergenceDivisible_of_steps`;
the uniqueness step proved by `obstacleLimitUniqueness`, x3, from the proved steps `matedCRTScalingConstantPositive`
and `obstacleLimitMaximumPrinciple`). -/
example (𝒮 : SpaceFillingSLEModel) (h48 : SubsequentialPropertiesStmt 𝒮) (h46 : SubsequentialConvergenceStmt 𝒮)
    (hmeas : ConvergenceDivisibleEventMeasurableStep 𝒮) : ConvergenceDivisibleStmt 𝒮 := by
  have huniq : ObstacleLimitUniquenessStep 𝒮 := obstacleLimitUniqueness 𝒮
  audit_apply convergenceDivisible_of_steps

/-- **Proposition 4.2** from Theorems 4.1, 2.3, Lemmas 2.13, 3.3, 2.8 and `ObstacleClusterInnerApproximationStep`
(`divSandpileLowerBound_of_steps`; the odometer comparison from `divSandpileOdometerComparison_of_cellsMeet`). -/
example (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮) (h23 : ConeHarmonicBallsStmt)
    (h213 : MaximumPrincipleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hin : ObstacleClusterInnerApproximationStep 𝒮) : DivSandpileLowerBoundStmt 𝒮 := by
  have hadj : AdjacentCellsMeetAeStep 𝒮 := adjacentCellsMeetAeStep 𝒮
  have hcmp : DivSandpileOdometerComparisonStep 𝒮 := by
    audit_apply divSandpileOdometerComparison_of_cellsMeet
  audit_apply divSandpileLowerBound_of_steps

/-- **Lemma 4.3** from `BallInteriorConnectedStep` (E-c1-2) (`discreteBasicProperties_of_inputs`). -/
example (𝒮 : SpaceFillingSLEModel) (hconn : BallInteriorConnectedStep 𝒮) : DiscreteBasicPropertiesStmt 𝒮 := by
  have hadj : AdjacentCellsMeetAeStep 𝒮 := adjacentCellsMeetAeStep 𝒮
  have hG : GreenKernelLaplacianStep := greenKernelLaplacianStep
  have hN : NormExitTimeLaplacianStep := normExitTimeLaplacianStep
  audit_apply discreteBasicProperties_of_inputs

/-- **Lemma 4.4**, corrected form (E-c1-1), from `BallInteriorConnectedStep`
(`discreteLaplacianBoundCorrected_of_inputs`). The Draft `DiscreteLaplacianBoundStmt` (OPEN, E-c1-1) has no reduction;
Lemmas 4.6, 4.8, 7.2 (corrected), 7.3 and 7.4 still consume it. -/
example (𝒮 : SpaceFillingSLEModel) (hconn : BallInteriorConnectedStep 𝒮) :
    DiscreteLaplacianBoundCorrectedStmt 𝒮 := by
  have hadj : AdjacentCellsMeetAeStep 𝒮 := adjacentCellsMeetAeStep 𝒮
  have hG : GreenKernelLaplacianStep := greenKernelLaplacianStep
  audit_apply discreteLaplacianBoundCorrected_of_inputs

/-- **Lemma 4.5**, corrected form (E-c1-1), from `BallInteriorConnectedStep`
(`discreteConservationOfMassCorrected_of_inputs`). -/
example (𝒮 : SpaceFillingSLEModel) (hconn : BallInteriorConnectedStep 𝒮) :
    DiscreteConservationOfMassCorrectedStmt 𝒮 := by
  have hadj : AdjacentCellsMeetAeStep 𝒮 := adjacentCellsMeetAeStep 𝒮
  have hG : GreenKernelLaplacianStep := greenKernelLaplacianStep
  audit_apply discreteConservationOfMassCorrected_of_inputs

/-- **Lemma 4.6** from Lemmas 4.7, 4.4 (Draft, E-c1-1), 3.1, 3.5 and three steps
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

/-- **Lemma 4.8** from Lemmas 3.3, 3.5, 3.7, 4.6, 4.3, 4.4 (Draft, E-c1-1), 2.13 and two steps
(`subsequentialProperties_of_steps`). -/
example (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮) (h37 : ConvergenceNormalizedExitTimeStmt 𝒮)
    (h46 : SubsequentialConvergenceStmt 𝒮) (h43 : DiscreteBasicPropertiesStmt 𝒮)
    (h44 : DiscreteLaplacianBoundStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
    (happ : OdometerObstacleApproximationStep 𝒮) (hlim : OdometerDistributionalLimitStep 𝒮) :
    SubsequentialPropertiesStmt 𝒮 := by
  audit_apply subsequentialProperties_of_steps

/-! ## Section 5 -/

/-- **Proposition 5.1** from Lemmas 2.7, 2.8, 5.3, 5.4, Theorems 4.1, 2.3, Lemmas 2.13, 3.3 and three steps
(`iDLALowerBound_of_inputs`; the discrete-cluster form of Proposition 4.2 from `discreteClusterInnerBound_of_steps`). -/
example (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h53 : MeanValueInequalityStmt 𝒮) (h54 : LLowerBoundStmt 𝒮) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h213 : MaximumPrincipleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (hE : EnvSigmaMeasurableStep 𝒮) (hin : ObstacleClusterInnerApproximationStep 𝒮)
    (hstop : IDLALowerBoundStoppedStep 𝒮) : IDLALowerBoundStmt 𝒮 := by
  have hI : DiscreteClusterInnerBoundStep 𝒮 := by audit_apply discreteClusterInnerBound_of_steps
  audit_apply iDLALowerBound_of_inputs

/-- **Lemma 5.2** from Lemmas 2.7, 2.8 and `EnvSigmaMeasurableStep` (E-c2-1) (`generalIDLALowerBound_of_inputs`). -/
example (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (hE : EnvSigmaMeasurableStep 𝒮) : GeneralIDLALowerBoundStmt 𝒮 := by
  audit_apply generalIDLALowerBound_of_inputs

/-- **Lemma 5.3** from Lemmas 4.4 (corrected), 2.13, 4.1, 3.3, 2.18 and `MeanValueSurplusStep`
(`meanValueInequality_of_surplus`; E-x1-1 boundary repair). -/
example (𝒮 : SpaceFillingSLEModel) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hsur : MeanValueSurplusStep 𝒮) : MeanValueInequalityStmt 𝒮 := by
  audit_apply meanValueInequality_of_surplus

/-- **Lemma 5.4** from the cited Lemmas 2.15, 2.16, 2.9 only (`lLowerBound_of_adjacentCellsMeet`). -/
example (𝒮 : SpaceFillingSLEModel) (h215 : GreenFunctionCrudeBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) : LLowerBoundStmt 𝒮 := by
  have hadj : AdjacentCellsMeetAeStep 𝒮 := adjacentCellsMeetAeStep 𝒮
  audit_apply lLowerBound_of_adjacentCellsMeet

/-! ## Section 6 -/

/-- **Lemma 6.3**, proved (`AbelianIDLA.abelianIDLA`). -/
example (𝒮 : SpaceFillingSLEModel) : AbelianIDLAStmt 𝒮 := AbelianIDLA.abelianIDLA 𝒮

/-- **Lemma 6.4** from Lemmas 6.6 (proved), 6.5 and two steps (`goodAnnulusPrevalence_of_restriction`; IR-c4-5 from
`ConeMeanZeroRestrictionStep` by `annulusIterateConeTransfer`). -/
example (h66 : AnnulusIterateStmt) (h65 : AnnulusHitStmt) (hR : ConeMeanZeroRestrictionStep)
    (hloc : GoodAnnulusEventLocalityStep) : GoodAnnulusPrevalenceStmt := by
  audit_apply goodAnnulusPrevalence_of_restriction

/-- **Lemma 6.5** from four whole-plane field steps (`annulusHit_of_steps`). -/
example (h1 : WholePlaneLQGExistenceStep) (h2 : ConeWholePlaneWeylComparisonStep)
    (h3 : WholePlaneLQGCoordinateChangeStep) (h4 : WholePlaneGoodAnnulusTightnessStep) : AnnulusHitStmt := by
  audit_apply annulusHit_of_steps

/-- **Lemma 6.6**, proved (`annulusIterate`, x4: `annulusIterate_of_leo` on Leonardo Bonanno's
`LQGMetric.LM.lmLem3_1a`, with the law transfer `annulusGFFLawTransfer : AnnulusGFFLawTransferStep`). -/
example : AnnulusIterateStmt := annulusIterate

/-- **Lemma 6.7** from Lemmas 6.8 (Draft, no log loss), 2.7, 2.8, 2.19 (`constantOrderLowerBound`). -/
example (𝒮 : SpaceFillingSLEModel) (h68 : ConstantOrderLowerBoundDivStmt 𝒮) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮) :
    ConstantOrderLowerBoundStmt 𝒮 := by
  have hadj : AdjacentCellsMeetAeStep 𝒮 := adjacentCellsMeetAeStep 𝒮
  audit_apply constantOrderLowerBound

/-- **Lemma 6.8**, E-A10 (b) form `ConstantOrderLowerBoundDivLogStmt` (`1 - s₂/(1+|log r|)²`), from Lemmas 2.16,
2.7, 2.8, 2.9, 6.4, 2.18, 2.19 and `GoodScaleEventMeasurableStep` (`constantOrderLowerBoundDiv_of_steps`). The Draft
`ConstantOrderLowerBoundDivStmt` has no reduction; Lemma 6.7 (Draft form), 6.9 (local rate) and Proposition 7.1
consume it. -/
example (𝒮 : SpaceFillingSLEModel) (h216 : GreenKernelLowerBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (h29 : CountingMeasureConvergenceStmt 𝒮) (h64 : GoodAnnulusPrevalenceStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮)
    (hmeas : GoodScaleEventMeasurableStep 𝒮) : ConstantOrderLowerBoundDivLogStmt 𝒮 := by
  have hadj : AdjacentCellsMeetAeStep 𝒮 := adjacentCellsMeetAeStep 𝒮
  audit_apply constantOrderLowerBoundDiv_of_steps

/-- **Lemma 6.9**, local-rate form `ChanceOfBeingAbsorbedLocalRateStmt` (E-c5-1), from Lemma 6.7
(`chanceOfBeingAbsorbedLocalRate`). The Draft `ChanceOfBeingAbsorbedStmt` implies it
(`ChanceOfBeingAbsorbedStmt.localRate`) but has no reduction. -/
example (𝒮 : SpaceFillingSLEModel) (h67 : ConstantOrderLowerBoundStmt 𝒮) :
    ChanceOfBeingAbsorbedLocalRateStmt 𝒮 := by
  audit_apply chanceOfBeingAbsorbedLocalRate

/-- **Lemma 6.7**, E-A10 (b) form `ConstantOrderLowerBoundLogStmt` (absorption probability `s₂/(1+|log r|)²`), from
Lemmas 6.8 (b), 2.7, 2.8, 2.19 (`constantOrderLowerBoundLog`). -/
example (𝒮 : SpaceFillingSLEModel) (h68 : ConstantOrderLowerBoundDivLogStmt 𝒮) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮) :
    ConstantOrderLowerBoundLogStmt 𝒮 := by
  have hadj : AdjacentCellsMeetAeStep 𝒮 := adjacentCellsMeetAeStep 𝒮
  audit_apply constantOrderLowerBoundLog

/-- **Lemma 6.9**, E-A10 (b) form `ChanceOfBeingAbsorbedLogLossStmt` (with `s₃` chosen after `s₀`, E-c5-1), from
Lemma 6.7 (b) (`chanceOfBeingAbsorbedLogLoss_of_steps`, the Chernoff step proved). -/
example (𝒮 : SpaceFillingSLEModel) (h67 : ConstantOrderLowerBoundLogStmt 𝒮) :
    ChanceOfBeingAbsorbedLogLossStmt 𝒮 := by
  have hC : AbsorptionChernoffStep := Absorption.absorptionChernoffStep
  audit_apply chanceOfBeingAbsorbedLogLoss_of_steps

/-- **Lemma 6.10** from Lemmas 6.8 (b), 2.7, 2.8, 2.19, through Lemmas 6.7 (b) and 6.9 (b) (`iterativeBound_of_div`;
`AdjacentCellsMeetStep` from `AdjacentCellsMeetAeStep.probTendsToOne`). -/
example (𝒮 : SpaceFillingSLEModel) (h68 : ConstantOrderLowerBoundDivLogStmt 𝒮) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮) : IterativeBoundStmt 𝒮 := by
  have hadj : AdjacentCellsMeetAeStep 𝒮 := adjacentCellsMeetAeStep 𝒮
  audit_apply iterativeBound_of_div

/-- **Theorem 6.1** from Lemma 6.10, Proposition 5.1 and `BoundaryLayerMeasurableStep` (E-c2-3)
(`IDLAUpperBound.iDLAUpperBound_of_steps`; Lemma 6.3 used in its proved form). -/
example (𝒮 : SpaceFillingSLEModel) (h610 : IterativeBoundStmt 𝒮) (h51 : IDLALowerBoundStmt 𝒮)
    (hm : BoundaryLayerMeasurableStep 𝒮) : IDLAUpperBoundStmt 𝒮 := by
  audit_apply IDLAUpperBound.iDLAUpperBound_of_steps

/-! ## Section 7 -/

/-! **Proposition 7.1** (`divSandpileUpperBound_of_carved_inputs`, MatedCRT/Steps/Sec7/DivSandpileUpperBound.lean:164)
is checked in docs/campaign/REDUCTIONS.md only: its module still cannot be imported together with Lemma 7.2's
(`MatedCRT.Sec7.vertexPoint_mem_cell` is declared both in MatedCRT/Proofs/Sec7/DivSandpileUpperBound/CrudeCells.lean
and in MatedCRT/Proofs/Sec7/MassBoundOdometer/Count.lean; "environment already contains", rechecked 2026-11-04
14:50Z). Once the duplicate is renamed, restore the import `MatedCRT.Steps.Sec7.DivSandpileUpperBound` and this
example (its hypothesis list was read from the environment at 14:56Z):

    example (𝒮 : SpaceFillingSLEModel) (h23 : ConeHarmonicBallsStmt) (h68 : ConstantOrderLowerBoundDivStmt 𝒮)
        (h27 : VolumeGrowthStmt) (h72 : MassBoundOdometerStmt 𝒮) (h41 : ConvergenceDivisibleStmt 𝒮)
        (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
        (h73 : OdometerBoundMassStmt 𝒮) (h74 : CrudeUpperBoundStmt 𝒮)
        (hset : StoppedObstacleSetupStep 𝒮) (hconf : StoppedShellConfinementStep 𝒮) :
        DivSandpileUpperBoundStmt 𝒮 := by
      audit_apply divSandpileUpperBound_of_carved_inputs

It consumes the Draft 7.2 `MassBoundOdometerStmt`, refuted by E-c3-2, and the Draft 6.8 (no log loss, E-A10), so it
is vacuous until it is rerouted through `MassBoundOdometerAboveScaleStmt` and `ConstantOrderLowerBoundDivLogStmt`. -/

/-- **Lemma 7.2**, corrected form `MassBoundOdometerAboveScaleStmt` (E-c3-2, `s ≥ ε^β`), from Lemmas 2.16, 2.8,
4.4 (Draft, E-c1-1) (`massBoundOdometerAboveScale_of_draft`). -/
example (𝒮 : SpaceFillingSLEModel) (h216 : GreenKernelLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h44 : DiscreteLaplacianBoundStmt 𝒮) : MassBoundOdometerAboveScaleStmt 𝒮 := by
  have hadj : AdjacentCellsMeetAeStep 𝒮 := adjacentCellsMeetAeStep 𝒮
  audit_apply massBoundOdometerAboveScale_of_draft

/-- **Lemma 7.3** from Lemma 4.4 (Draft, E-c1-1) (`odometerBoundMass_of_draft`). -/
example (𝒮 : SpaceFillingSLEModel) (h44 : DiscreteLaplacianBoundStmt 𝒮) : OdometerBoundMassStmt 𝒮 := by
  have hadj : AdjacentCellsMeetAeStep 𝒮 := adjacentCellsMeetAeStep 𝒮
  audit_apply odometerBoundMass_of_draft

/-- **Lemma 7.4** from Lemma 4.4 (Draft, E-c1-1) and the literature input `DegreeBoundInput`
(`crudeUpperBound_of_draft`). -/
example (𝒮 : SpaceFillingSLEModel) (h44 : DiscreteLaplacianBoundStmt 𝒮) (hdeg : DegreeBoundInput 𝒮) :
    CrudeUpperBoundStmt 𝒮 := by
  have hadj : AdjacentCellsMeetAeStep 𝒮 := adjacentCellsMeetAeStep 𝒮
  audit_apply crudeUpperBound_of_draft

/-! ## Appendix A: proved -/

/-- **Lemma A.1**, proved. -/
example : DiscreteDivergenceTheoremStmt := discreteDivergenceTheorem

/-- **Lemma A.2**, proved. -/
example : DiscreteBasicPropertiesGeneralStmt := discreteBasicPropertiesGeneral

/-- **Lemma A.3**, proved. -/
example : DiscreteLaplacianBoundGeneralStmt := discreteLaplacianBoundGeneral

/-- **Lemma A.4**, proved. -/
example : DiscreteConservationOfMassGeneralStmt := discreteConservationOfMassGeneral

end MatedCRT.Audit
