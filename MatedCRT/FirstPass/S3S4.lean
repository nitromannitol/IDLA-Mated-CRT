import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Final
import MatedCRT.Proofs.Sec4.ObstacleSpecialization.Final
import MatedCRT.Proofs.Sec4.SubsequentialProperties.Final
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Steps.Sec2.MaximumPrinciple
import MatedCRT.Steps.Sec2.BoundedExitTimeRV
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.InteriorStep
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.BoundaryStep
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.AlmostSureInterior
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.DyadicModulus
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.Final
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ExitCell
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.PathFunctionalStep
import MatedCRT.Proofs.Sec4.SubsequentialProperties.PreparedInputs
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.PreparedConeScaling
import MatedCRT.FirstPass.Frozen.S3S4
import MatedCRT.FirstPass.Frozen.S3c
import MatedCRT.FirstPass.S3c.ExitTimeCore

/-!
# First pass: paper-owned results of Sections 3 and 4

Each `firstPass_<section>_<number>` takes as hypotheses only Draft statements of numbered results used by the printed
(or corrected) proof, the frozen external inputs of `MatedCRT/FirstPass/Frozen/S3S4.lean` and the existing External
inputs (`MepsScalingInput`). Cited results (Lemma 3.2, Lemmas 2.7, 2.18) get no theorem of their own.
-/

namespace MatedCRT

/-- **Lemma 3.1** (lemma:discrete-potential-tightness), corrected form (C3, C11; `DiscretePotentialTightnessCorrectedStmt`,
since the printed Draft is false). Hypotheses: `MepsScalingInput` (External, eq:meps-scaling), Lemma 2.7
(`VolumeGrowthStmt`), the first clause of Lemma 2.18 in the per-model form `BG20Prop51 𝒮` (frozen, BG20 Proposition 5.1,
`FirstPass/Frozen/S3c.lean`, replacing `ExitTimeUpperBoundStmt 𝒮`) and the frozen corrected
Lemma 3.2. The second clause of Lemma 2.18 is derived by `exitTimeUpperBoundStmt_core` (FirstPass/S3c/ExitTimeCore.lean). -/
theorem firstPass_3_1_corrected {𝒮 : SpaceFillingSLEModel} (hm : MepsScalingInput 𝒮) (h27 : VolumeGrowthStmt)
    (hBG : BG20Prop51 𝒮) (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) :
    DiscretePotentialTightnessCorrectedStmt 𝒮 :=
  discretePotentialTightnessCorrected_of_inputs hm h27 (exitTimeUpperBoundStmt_core hBG h27) h32

/-- **Lemma 4.3** (lemma:discrete-basic-properties, paper line 1690). No hypothesis. -/
theorem firstPass_4_3 (𝒮 : SpaceFillingSLEModel) : DiscreteBasicPropertiesStmt 𝒮 :=
  discreteBasicProperties 𝒮

/-- **Lemma 4.4** (lemma:discrete-laplacian-bound, paper line 1708), corrected form (C7: the origin clause needs
`0 ∈ V^ε(B_ρ) \ V^ε(∂B_ρ)`; `DiscreteLaplacianBoundCorrectedStmt`). No hypothesis. -/
theorem firstPass_4_4_corrected (𝒮 : SpaceFillingSLEModel) : DiscreteLaplacianBoundCorrectedStmt 𝒮 :=
  discreteLaplacianBoundCorrected 𝒮

/-- **Lemma 4.5** (lemma:discrete-conservation-of-mass, paper line 1716), corrected form (C7;
`DiscreteConservationOfMassCorrectedStmt`). No hypothesis. -/
theorem firstPass_4_5_corrected (𝒮 : SpaceFillingSLEModel) : DiscreteConservationOfMassCorrectedStmt 𝒮 :=
  discreteConservationOfMassCorrected 𝒮

/-- **Lemma 4.7** (lemma:equibounded, paper line 1740). Hypotheses: Lemma 2.7 (`VolumeGrowthStmt`), Lemma 2.18
(`ExitTimeUpperBoundStmt`) and `MepsScalingInput` (External). -/
theorem firstPass_4_7 {𝒮 : SpaceFillingSLEModel} (h27 : VolumeGrowthStmt) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hm : MepsScalingInput 𝒮) : EquiboundedStmt 𝒮 :=
  equibounded_of_inputs h27 h218 hm

/-- **Lemma 3.3** (lemma:uniform-convergence-of-greens-function), uniform convergence of the rescaled discrete Green kernel
away from the pole. Hypotheses: Draft Lemmas 2.10 (`DegreeMeasureConvergenceStmt`), 3.4 (`IntegralConvergenceGreenFunctionStmt`),
2.14 (`GreenKernelUpperBoundStmt`), 2.8 (`CellSizeEstimateStmt`); Lemma 2.7 and 2.18 and `MepsScalingInput` (External) and the
frozen corrected Lemma 3.2 feed the a.s. form of Lemma 3.1 (`discretePotentialTightnessAeStep_of_inputs`, proved). The interior and
boundary steps are proved (`greenKernelInteriorStep`, `greenKernelBoundaryStep`) and used in `uniformConvergenceGreenKernel_final`. -/
theorem firstPass_3_3 {𝒮 : SpaceFillingSLEModel} (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h27 : VolumeGrowthStmt) (h218 : ExitTimeUpperBoundStmt 𝒮) (hm : MepsScalingInput 𝒮)
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) : UniformConvergenceGreenKernelStmt 𝒮 :=
  uniformConvergenceGreenKernel_final 𝒮 h210 h34 h214 h28
    (discretePotentialTightnessAeStep_of_inputs hm (boundedExitTimeRV_of_steps h27) h218 h32)

/-- **Lemma 3.7** (lemma:convergence-of-the-normalized-exit-time). Hypotheses: Draft Lemmas 3.3 and 3.5 (numbered results,
passed as hypotheses), Lemma 2.7 (`VolumeGrowthStmt`), Lemma 2.18 (`ExitTimeUpperBoundStmt`), `MepsScalingInput` (External)
and the frozen corrected Lemma 3.2. The a.s. interior potential tightness `DiscretePotentialTightnessAeStep` is proved from
these inputs by `discretePotentialTightnessAeStep_of_inputs`. -/
theorem firstPass_3_7 {𝒮 : SpaceFillingSLEModel} (h27 : VolumeGrowthStmt) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hm : MepsScalingInput 𝒮) (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮) :
    ConvergenceNormalizedExitTimeStmt 𝒮 :=
  convergenceNormalizedExitTime_of_statements 𝒮 h33 h35 (boundedExitTimeRV_of_steps h27) h218
    (discretePotentialTightnessAeStep_of_inputs hm (boundedExitTimeRV_of_steps h27) h218 h32)

/-- **Lemma 3.6** (lemma:convergence-of-harmonic-functions), in its printed (pointwise, Hölder datum on a neighbourhood of the
closed disk) form `ConvergenceHarmonicFunctionsStmt`. Hypotheses: Draft Lemma 2.11 (`RandomWalkToLBMStmt`, cited), Lemma 2.8
(`CellSizeEstimateStmt`, cited), `MepsScalingInput` (External) and the frozen regular-exit input of planar Brownian motion. The path
step uses the proved measurability `interpolatedWalkMeasurableStep` (inside `harmonicPathExitStep_of_inputs`) and the proved
`lbmPathFunctionalMeasurableStep_holds`; the exit-cell comparison is `harmonicExitCellStep_of_inputs`. The corrected Lemma 3.6 of
[C13] (uniform convergence and same-walk comparison) is NOT this theorem; see the report. -/
theorem firstPass_3_6 {𝒮 : SpaceFillingSLEModel} (h211 : RandomWalkToLBMStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hm : MepsScalingInput 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit) :
    ConvergenceHarmonicFunctionsStmt 𝒮 :=
  convergenceHarmonicFunctions_of_steps 𝒮 h211 h28 (harmonicPathExitStep_of_inputs 𝒮 hexc (lbmPathFunctionalMeasurableStep_holds 𝒮))
    (harmonicExitCellStep_of_inputs 𝒮 h211 hm hexc (lbmPathFunctionalMeasurableStep_holds 𝒮))

/-- **Lemma 4.6** (lemma:subsequential-convergence), corrected fixed-sequence form [C12]: `SubsequentialConvergencePreparedStmt`
(Draft/Section4Prepared.lean; the fixed time and deterministic sequence precede the deterministic thinning and its almost sure
event). The printed quantifier order is not established; the printed Draft
`SubsequentialConvergenceStmt` is not proved here. Hypotheses: Lemma 2.7, Lemma 2.18, Draft Lemmas 3.5 and 3.7 (numbered results,
as hypotheses), `MepsScalingInput` (External) and the frozen corrected Lemma 3.2. Lemma 4.7 and Lemma 4.4 (corrected) are
`firstPass_4_7` and `firstPass_4_4_corrected`; Lemma 2.17 is `boundedExitTimeRV_of_steps`. Proof: the prepared estimates
`subsequentialConvergencePrepared_of_estimates`, which has no further step hypothesis. -/
theorem firstPass_4_6_corrected {𝒮 : SpaceFillingSLEModel} (hm : MepsScalingInput 𝒮) (h27 : VolumeGrowthStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮) (h37 : ConvergenceNormalizedExitTimeStmt 𝒮) :
    SubsequentialConvergencePreparedStmt 𝒮 :=
  subsequentialConvergencePrepared_of_estimates 𝒮 hm (firstPass_4_7 h27 h218 hm) (firstPass_4_4_corrected 𝒮) h35 h218 hH
    h37 (boundedExitTimeRV_of_steps h27) h27

/-- RETIRED (FALSE: the hypothesis `FrozenConeEnvironmentScaling` is FALSE). The repaired statement, with `FrozenConeScalingLaw`, is `firstPass_4_1_coneLaw`
(FirstPass/S4S6c.lean). Kept for the record; do not delete.
**Theorem 4.1** (theorem:convergence-divisible), Draft form `ConvergenceDivisibleStmt`, through the prepared discrete
estimates (corrected fixed-time proof, C11/C12). Hypotheses: Draft Lemmas 2.10, 3.4, 2.14, 2.8, 3.5 and 2.18, 2.7 (numbered
results, the first three cited); `MepsScalingInput` (External); the frozen corrected Lemma 3.2 and the frozen
`ConeEnvironmentScalingStep`. -/
theorem firstPass_4_1 {𝒮 : SpaceFillingSLEModel} (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeEnvironmentScaling 𝒮) :
    ConvergenceDivisibleStmt 𝒮 :=
  convergenceDivisible_of_prepared_discrete_coneScaling 𝒮 hm h210 h34 h214 h28 h35 h218 hH h27 hcone

/-- **Lemma 4.8** (lemma:subsequential-properties). Hypotheses: the Draft statements of Lemmas 3.3, 3.5 and 3.7, which
are numbered results of this first pass (their first-pass theorems are the same statements, as hypotheses here).
Lemma 2.13 (`MaximumPrincipleStmt`, corrected [C2]) is discharged by `maximumPrinciple_of_steps` with
`adjacentCellsMeetAeStep`. -/
theorem firstPass_4_8 {𝒮 : SpaceFillingSLEModel} (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮) (h37 : ConvergenceNormalizedExitTimeStmt 𝒮) :
    SubsequentialPropertiesStmt 𝒮 :=
  subsequentialProperties_of_inputs 𝒮 h33 h35 h37 (maximumPrinciple_of_steps (adjacentCellsMeetAeStep 𝒮))

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.firstPass_3_1_corrected
#print axioms MatedCRT.firstPass_4_3
#print axioms MatedCRT.firstPass_4_4_corrected
#print axioms MatedCRT.firstPass_4_5_corrected
#print axioms MatedCRT.firstPass_4_7
#print axioms MatedCRT.firstPass_4_8
#print axioms MatedCRT.firstPass_3_3
#print axioms MatedCRT.firstPass_3_7
#print axioms MatedCRT.firstPass_3_6
#print axioms MatedCRT.firstPass_4_6_corrected
#print axioms MatedCRT.firstPass_4_1
