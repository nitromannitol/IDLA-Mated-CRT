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

/-!
# Audit: the current reductions of the numbered results

For every numbered result of "Internal DLA on mated-CRT maps" (arXiv:2211.04891) whose reduction is committed, an
`example` restates the best current reduction with its exact hypothesis list: the Draft statements of other numbered
results (`...Stmt`, `MatedCRT/Draft`), the literature inputs (`...Input`, `MatedCRT/External`) and the open step
Props (`...Step`, `MatedCRT/Steps`). Every proved step is discharged inside the example. If a Draft statement, a
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
`MatedCRT.Defs.Map`) and Lemma 6.6 (`LQGMetric.LM.lmLem3_1a`, `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`, via
`MatedCRT.Steps.Sec6.AnnulusIterate`).
-/

/-- `audit_apply e`: apply the reduction theorem `e` and close each of its hypotheses by a hypothesis of the
`example`; a new hypothesis of `e` makes the example fail. -/
macro "audit_apply " e:term : tactic => `(tactic| (apply $e <;> assumption))

namespace MatedCRT.Audit

/-! ## Section 2 -/

/-- **Theorem 2.3** from Lemmas 2.4, 2.5 and `ConeFamilyAEMeasurableStep` (`coneHarmonicBalls_of_steps`). -/
example (h24 : ConeHarmonicBallsUpToFixedTimeStmt) (h25 : ConeScaleInvarianceUpToFixedTimeStmt)
    (hfam : ConeFamilyAEMeasurableStep) : ConeHarmonicBallsStmt := by
  audit_apply coneHarmonicBalls_of_steps

/-- **Lemma 2.13** from `AdjacentCellsMeetAeStep` (`maximumPrinciple_of_steps`). -/
example (𝒮 : SpaceFillingSLEModel) (hadj : AdjacentCellsMeetAeStep 𝒮) : MaximumPrincipleStmt 𝒮 := by
  audit_apply maximumPrinciple_of_steps

/-- **Lemma 2.17** from Lemma 2.7 (`boundedExitTimeRV_of_steps`). -/
example (h27 : VolumeGrowthStmt) : BoundedExitTimeRVStmt := by
  audit_apply boundedExitTimeRV_of_steps

/-- **Lemma 2.19** from Lemmas 2.7 and 2.18 (`expectedExitTimeExplicitBound_of_steps`, through Lemma 2.17). -/
example (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) (h218 : ExitTimeUpperBoundStmt 𝒮) :
    ExpectedExitTimeExplicitBoundStmt 𝒮 := by
  have h217 : BoundedExitTimeRVStmt := by audit_apply boundedExitTimeRV_of_steps
  audit_apply expectedExitTimeExplicitBound_of_steps

/-! ## Section 4 -/

/-- **Theorem 4.1** from Lemmas 4.6, 4.8 and three steps (`convergenceDivisible_of_steps`; the uniqueness step from
`obstacleLimitUniqueness_of_steps` and `obstacleLimitRegularity_of_steps`). -/
example (𝒮 : SpaceFillingSLEModel) (h48 : SubsequentialPropertiesStmt 𝒮) (h46 : SubsequentialConvergenceStmt 𝒮)
    (hm : MatedCRTScalingConstantPositiveStep 𝒮) (hmax : ObstacleLimitMaximumPrincipleStep 𝒮)
    (hmeas : ConvergenceDivisibleEventMeasurableStep 𝒮) : ConvergenceDivisibleStmt 𝒮 := by
  have hreg : ObstacleLimitRegularityStep 𝒮 := by audit_apply obstacleLimitRegularity_of_steps
  have huniq : ObstacleLimitUniquenessStep 𝒮 := by audit_apply obstacleLimitUniqueness_of_steps
  audit_apply convergenceDivisible_of_steps

/-- **Proposition 4.2** from Theorems 4.1, 2.3, Lemmas 2.13, 3.3, 2.8, `ObstacleClusterInnerApproximationStep` and
`AdjacentCellsMeetAeStep` (`divSandpileLowerBound_of_steps`; the odometer comparison from
`divSandpileOdometerComparison_of_cellsMeet`). -/
example (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮) (h23 : ConeHarmonicBallsStmt)
    (h213 : MaximumPrincipleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hin : ObstacleClusterInnerApproximationStep 𝒮) (hadj : AdjacentCellsMeetAeStep 𝒮) :
    DivSandpileLowerBoundStmt 𝒮 := by
  have hcmp : DivSandpileOdometerComparisonStep 𝒮 := by
    audit_apply divSandpileOdometerComparison_of_cellsMeet
  audit_apply divSandpileLowerBound_of_steps

/-- **Lemma 4.3** from `BallInteriorConnectedStep` (E-c1-2) and `AdjacentCellsMeetAeStep`
(`discreteBasicProperties_of_inputs`). -/
example (𝒮 : SpaceFillingSLEModel) (hconn : BallInteriorConnectedStep 𝒮) (hadj : AdjacentCellsMeetAeStep 𝒮) :
    DiscreteBasicPropertiesStmt 𝒮 := by
  have hG : GreenKernelLaplacianStep := greenKernelLaplacianStep
  have hN : NormExitTimeLaplacianStep := normExitTimeLaplacianStep
  audit_apply discreteBasicProperties_of_inputs

/-- **Lemma 4.4**, corrected form (E-c1-1), from `BallInteriorConnectedStep` and `AdjacentCellsMeetAeStep`
(`discreteLaplacianBoundCorrected_of_inputs`). The Draft `DiscreteLaplacianBoundStmt` (OPEN, E-c1-1) has no reduction;
Lemmas 4.6, 4.8, 7.2 (corrected), 7.3 and 7.4 still consume it. -/
example (𝒮 : SpaceFillingSLEModel) (hconn : BallInteriorConnectedStep 𝒮) (hadj : AdjacentCellsMeetAeStep 𝒮) :
    DiscreteLaplacianBoundCorrectedStmt 𝒮 := by
  have hG : GreenKernelLaplacianStep := greenKernelLaplacianStep
  audit_apply discreteLaplacianBoundCorrected_of_inputs

/-- **Lemma 4.5**, corrected form (E-c1-1), from `BallInteriorConnectedStep` and `AdjacentCellsMeetAeStep`
(`discreteConservationOfMassCorrected_of_inputs`). -/
example (𝒮 : SpaceFillingSLEModel) (hconn : BallInteriorConnectedStep 𝒮) (hadj : AdjacentCellsMeetAeStep 𝒮) :
    DiscreteConservationOfMassCorrectedStmt 𝒮 := by
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

/-- **Lemma 5.3** from Lemmas 4.4 (corrected), 2.13, 4.1, 3.3, 2.18 and `MeanValueNormalizedStep`
(`meanValueInequality_of_steps`). -/
example (𝒮 : SpaceFillingSLEModel) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hmv : MeanValueNormalizedStep 𝒮) : MeanValueInequalityStmt 𝒮 := by
  audit_apply meanValueInequality_of_steps

/-- **Lemma 5.4** from Lemmas 2.15, 2.16, 2.9 and `LLowerBoundLocalStep` (`lLowerBound_of_local`). -/
example (𝒮 : SpaceFillingSLEModel) (h215 : GreenFunctionCrudeBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (hloc : LLowerBoundLocalStep 𝒮) : LLowerBoundStmt 𝒮 := by
  audit_apply lLowerBound_of_local

/-! ## Section 6 -/

/-- **Lemma 6.3**, proved (`AbelianIDLA.abelianIDLA`). -/
example (𝒮 : SpaceFillingSLEModel) : AbelianIDLAStmt 𝒮 := AbelianIDLA.abelianIDLA 𝒮

/-- **Lemma 6.4** from Lemmas 6.6, 6.5 and two steps (`goodAnnulusPrevalence_of_steps`). -/
example (h66 : AnnulusIterateStmt) (h65 : AnnulusHitStmt) (htr : AnnulusIterateConeTransferStep)
    (hloc : GoodAnnulusEventLocalityStep) : GoodAnnulusPrevalenceStmt := by
  audit_apply goodAnnulusPrevalence_of_steps

/-- **Lemma 6.5** from four whole-plane field steps (`annulusHit_of_steps`). -/
example (h1 : WholePlaneLQGExistenceStep) (h2 : ConeWholePlaneWeylComparisonStep)
    (h3 : WholePlaneLQGCoordinateChangeStep) (h4 : WholePlaneGoodAnnulusTightnessStep) : AnnulusHitStmt := by
  audit_apply annulusHit_of_steps

/-- **Lemma 6.6** from `AnnulusGFFLawTransferStep` (`annulusIterate_of_leo`, on Leonardo Bonanno's
`LQGMetric.LM.lmLem3_1a`). -/
example (htr : AnnulusGFFLawTransferStep) : AnnulusIterateStmt := by
  audit_apply annulusIterate_of_leo

/-- **Lemma 6.7** from Lemmas 6.8 (Draft, no log loss), 2.7, 2.8, 2.19 and `AdjacentCellsMeetAeStep`
(`constantOrderLowerBound`). -/
example (𝒮 : SpaceFillingSLEModel) (h68 : ConstantOrderLowerBoundDivStmt 𝒮) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮)
    (hadj : AdjacentCellsMeetAeStep 𝒮) : ConstantOrderLowerBoundStmt 𝒮 := by
  audit_apply constantOrderLowerBound

/-- **Lemma 6.8**, E-A10 (b) form `ConstantOrderLowerBoundDivLogStmt` (`1 - s₂/(1+|log r|)²`), from Lemmas 2.16,
2.7, 2.8, 2.9, 6.4, 2.18, 2.19 and two steps (`constantOrderLowerBoundDiv_of_steps`). The Draft
`ConstantOrderLowerBoundDivStmt` has no reduction; Lemmas 6.7, 6.9 and Proposition 7.1 consume it. -/
example (𝒮 : SpaceFillingSLEModel) (h216 : GreenKernelLowerBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (h29 : CountingMeasureConvergenceStmt 𝒮) (h64 : GoodAnnulusPrevalenceStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮)
    (hmeas : GoodScaleEventMeasurableStep 𝒮) (hadj : AdjacentCellsMeetAeStep 𝒮) :
    ConstantOrderLowerBoundDivLogStmt 𝒮 := by
  audit_apply constantOrderLowerBoundDiv_of_steps

/-- **Lemma 6.9**, local-rate form `ChanceOfBeingAbsorbedLocalRateStmt` (E-c5-1), from Lemma 6.7
(`chanceOfBeingAbsorbedLocalRate`). The Draft `ChanceOfBeingAbsorbedStmt` implies it
(`ChanceOfBeingAbsorbedStmt.localRate`) but has no reduction. -/
example (𝒮 : SpaceFillingSLEModel) (h67 : ConstantOrderLowerBoundStmt 𝒮) :
    ChanceOfBeingAbsorbedLocalRateStmt 𝒮 := by
  audit_apply chanceOfBeingAbsorbedLocalRate

/-- **Lemma 6.7**, E-A10 (b) form `ConstantOrderLowerBoundLogStmt` (absorption probability `s₂/(1+|log r|)²`), from
Lemmas 6.8 (b), 2.7, 2.8, 2.19 and `AdjacentCellsMeetAeStep` (`constantOrderLowerBoundLog`). -/
example (𝒮 : SpaceFillingSLEModel) (h68 : ConstantOrderLowerBoundDivLogStmt 𝒮) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮)
    (hadj : AdjacentCellsMeetAeStep 𝒮) : ConstantOrderLowerBoundLogStmt 𝒮 := by
  audit_apply constantOrderLowerBoundLog

/-- **Lemma 6.9**, E-A10 (b) form `ChanceOfBeingAbsorbedLogLossStmt` (with `s₃` chosen after `s₀`, E-c5-1), from
Lemma 6.7 (b) (`chanceOfBeingAbsorbedLogLoss_of_steps`, the Chernoff step proved). -/
example (𝒮 : SpaceFillingSLEModel) (h67 : ConstantOrderLowerBoundLogStmt 𝒮) :
    ChanceOfBeingAbsorbedLogLossStmt 𝒮 := by
  have hC : AbsorptionChernoffStep := Absorption.absorptionChernoffStep
  audit_apply chanceOfBeingAbsorbedLogLoss_of_steps

/-- **Lemma 6.10** from Lemmas 6.8 (b), 2.7, 2.8, 2.19 and `AdjacentCellsMeetAeStep` (IR-A2), through Lemmas 6.7 (b)
and 6.9 (b) (`iterativeBound_of_div`; `AdjacentCellsMeetStep` from `AdjacentCellsMeetAeStep.probTendsToOne`). -/
example (𝒮 : SpaceFillingSLEModel) (h68 : ConstantOrderLowerBoundDivLogStmt 𝒮) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮)
    (hadj : AdjacentCellsMeetAeStep 𝒮) : IterativeBoundStmt 𝒮 := by
  audit_apply iterativeBound_of_div

/-! ## Section 7 -/

/-! **Proposition 7.1** (`divSandpileUpperBound_of_carved_steps`, MatedCRT/Steps/Sec7/DivSandpileUpperBound.lean)
is checked in docs/campaign/REDUCTIONS.md only: its module cannot be imported together with Lemma 7.2's
(`MatedCRT.Sec7.vertexPoint_mem_cell` is declared both in MatedCRT/Proofs/Sec7/DivSandpileUpperBound/CrudeCells.lean
and in MatedCRT/Proofs/Sec7/MassBoundOdometer/Count.lean; "environment already contains", 2026-11-04 14:19Z). Once the
duplicate is renamed, restore the import `MatedCRT.Steps.Sec7.DivSandpileUpperBound` and this example:

    example (𝒮 : SpaceFillingSLEModel) (h23 : ConeHarmonicBallsStmt) (h68 : ConstantOrderLowerBoundDivStmt 𝒮)
        (h27 : VolumeGrowthStmt) (h72 : MassBoundOdometerStmt 𝒮) (h41 : ConvergenceDivisibleStmt 𝒮)
        (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
        (h73 : OdometerBoundMassStmt 𝒮) (h74 : CrudeUpperBoundStmt 𝒮) (hadj : AdjacentCellsMeetAeStep 𝒮)
        (hset : StoppedObstacleSetupStep 𝒮) (hconf : StoppedShellConfinementStep 𝒮) :
        DivSandpileUpperBoundStmt 𝒮 := by
      audit_apply divSandpileUpperBound_of_carved_steps

It consumes the Draft 7.2 `MassBoundOdometerStmt`, refuted by E-c3-2, so it is vacuous until it is rerouted through
`MassBoundOdometerAboveScaleStmt` (lc-checked at 09:57Z). -/

/-- **Lemma 7.2**, corrected form `MassBoundOdometerAboveScaleStmt` (E-c3-2, `s ≥ ε^β`), from Lemmas 2.16, 2.8,
4.4 (Draft, E-c1-1) and `AdjacentCellsMeetAeStep` (`massBoundOdometerAboveScale_of_draft`). -/
example (𝒮 : SpaceFillingSLEModel) (h216 : GreenKernelLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h44 : DiscreteLaplacianBoundStmt 𝒮) (hadj : AdjacentCellsMeetAeStep 𝒮) :
    MassBoundOdometerAboveScaleStmt 𝒮 := by
  audit_apply massBoundOdometerAboveScale_of_draft

/-- **Lemma 7.3** from Lemma 4.4 (Draft, E-c1-1) and `AdjacentCellsMeetAeStep` (`odometerBoundMass_of_draft`). -/
example (𝒮 : SpaceFillingSLEModel) (h44 : DiscreteLaplacianBoundStmt 𝒮) (hadj : AdjacentCellsMeetAeStep 𝒮) :
    OdometerBoundMassStmt 𝒮 := by
  audit_apply odometerBoundMass_of_draft

/-- **Lemma 7.4** from Lemma 4.4 (Draft, E-c1-1), the literature input `DegreeBoundInput` and
`AdjacentCellsMeetAeStep` (`crudeUpperBound_of_draft`). -/
example (𝒮 : SpaceFillingSLEModel) (h44 : DiscreteLaplacianBoundStmt 𝒮) (hdeg : DegreeBoundInput 𝒮)
    (hadj : AdjacentCellsMeetAeStep 𝒮) : CrudeUpperBoundStmt 𝒮 := by
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
