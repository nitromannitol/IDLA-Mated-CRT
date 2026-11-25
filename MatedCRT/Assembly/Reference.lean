import MatedCRT.Assembly.Remaining
import MatedCRT.Assembly.Canonical
import MatedCRT.FirstPass.Derived.GreenKernelUpperOfReference
import MatedCRT.FirstPass.Derived.ResistanceBoundOfReference
import MatedCRT.FirstPass.Derived.DiscreteHolderOfReference
import MatedCRT.FirstPass.Derived.MepsScalingOfLower
import MatedCRT.FirstPass.Derived.CoreGffLowerOfLemma69
import MatedCRT.FirstPass.S6j.ExitTimeLowerTail
import MatedCRT.FirstPass.Derived.RandomWalkToLBMStmtOfBG20
import MatedCRT.FirstPass.Derived.HN9OfChartField
import MatedCRT.Steps.Sec2.BoundedExitTimeRV
import MatedCRT.FirstPass.Derived.CanonicalHasReferenceEnvironments
import MatedCRT.FirstPass.Derived.WholePlaneClockFixedStartOfLocalLimit
import MatedCRT.FirstPass.Derived.WholePlaneClockStrictMonoOfOneStart
import MatedCRT.FirstPass.Derived.CanonicalCountedFormsOfCoupling
import MatedCRT.FirstPass.Derived.CanonicalCountedFormsOfCouplingClock
import MatedCRT.FirstPass.Derived.CanonicalInputsOfCoupling
import MatedCRT.FirstPass.Derived.GMS21UniformStartOfSelectedProkhorov
import MatedCRT.FirstPass.Derived.DegreeBoundOfLemma25Tail
import MatedCRT.FirstPass.SLERef.CertifiedCore
import MatedCRT.FirstPass.Derived.Counted
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.StepsOfDraft
import MatedCRT.FirstPass.Derived.OneSidedBoundaryOfReference
import MatedCRT.FirstPass.Derived.QuantumConeScalingDimension
import MatedCRT.Proofs.Sec5.StoppedPoleReduction
import MatedCRT.Proofs.Sec5.StoppedLayerBound
import MatedCRT.Proofs.Sec5.StoppedMissingSitesProof
import MatedCRT.Proofs.Sec4.Prop42Closure.Assembly

/-!
# The cited fields of `MainHypotheses` from reference environments

`ReferenceInputs 𝒮 ν` collects, for a model `𝒮`, a normalized space-filling SLE law `ν` of `𝒮`, the SLE closure
inputs, valid environments on `ℝ` (`HasReferenceEnvironments 𝒮`), the uniform-start invariance principle
(`GMS21UniformStartInput 𝒮`) and the chart forms of Berestycki-Gwynne, Lemmas 7.20 and 7.21
(`BG20ChartFieldInput 𝒮`). From these, seven fields of `RemainingHypotheses 𝒮` (`MatedCRT/Assembly/Remaining.lean`)
are theorems: Theorem 2.11 (`randomWalkToLBM`), Lemmas 2.14 and 2.16 (`greenKernelUpperBound`,
`greenKernelLowerBound`), the scaling of the expected exit time (`mepsScaling`), the corrected Lemma 3.2
(`discreteHolderContinuityCorrected`), Lemma 3.4 (`integralConvergenceGreenFunction`) and the lower surplus estimate
of Lemma 5.3 (`meanValueSurplusLower`), and so are the interior and boundary steps of Lemma 3.5
(`dirichletInterior`, `dirichletBoundary`) and the measurable selection of Lemma 4.6 (`odometerMeasurableSelection`;
see below):

* Theorem 2.11: `randomWalkToLBMStmt_of_markovLimit_bg20ChartField`;
* Lemmas 2.14 and 2.16: `FirstPass.Derived.greenKernelUpperBoundStmt_of_reference` and
  `FirstPass.Derived.greenKernelLowerBoundStmt_of_reference`, with the full one-sided mating-rigid set
  `exists_matingRigidLEOn_full_derived`;
* the scaling of the expected exit time: `mepsScalingInput_of_lower`, with Lemma 2.18 from Lemma 2.14, Lemma 2.17
  from the volume growth, and the lower half of Berestycki-Gwynne (1.8) from Lemmas 2.14, 2.16 and
  Berestycki-Gwynne Lemma 6.9 (`FirstPass.Derived.mεCdf_lower_of_lemma69`,
  `ExitTimeLowerTail.exitTimeLowerTail_of_uniformStart`);
* the corrected Lemma 3.2: `FirstPass.Derived.frozenDiscreteHolderContinuityCorrected_of_reference`;
* Lemma 3.4 and the lower surplus estimate of Lemma 5.3: `integralConvergenceGreenFunction_of_walk` and
  `meanValueSurplusLowerStep_of_meps` (`MatedCRT/Assembly/ProvedSteps.lean`).

The same inputs give the certified reference model `CertifiedReferenceModel ν 𝒮` of the counted forms of
docs/campaign/COUNTED.md (`ReferenceInputs.certifiedReferenceModel`), hence the corrected and the Draft Lemma 3.5
(`ReferenceInputs.discreteDirichletProblem`), and with it the two steps of Lemma 3.5
(`dirichletInteriorStep_of_draft`, `dirichletBoundaryStep_of_draft`,
`MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/StepsOfDraft.lean`), and the prepared Lemma 4.6
(`ReferenceInputs.subsequentialConvergencePrepared`), and with it the measurable selection
(`odometerMeasurableSelectionStep_of_prepared`). They also give the one-sided boundary continuity of Lemma 3.6
(`ReferenceInputs.oneSidedBoundaryContinuity`, from Lemma 3.11 of GMS19 in the reference environments), hence the
corrected Lemma 3.6 (`ReferenceInputs.correctedHarmonicConvergence`).

The geometry and margin steps of Proposition 5.1 hold for every model (`StoppedGeometry.stoppedInteriorGeometryStep_holds`,
`StoppedCode.stoppedInteriorMeasurableStep_holds`: the harmonic ball `Λ_t` is a Borel function of a field-measurable
version of `μ_h`, through the Lusin-Souslin decoder of the obstacle problem). With them the pole step follows from these
inputs (`ReferenceInputs.stoppedSurplusPole`), and the number of missing sites follows from Proposition 4.2
(`ReferenceInputs.stoppedMissingSites`), hence the layer step (`ReferenceInputs.stoppedLayerPotential`). The remaining
fields are the four open steps collected in `OpenStepHypotheses 𝒮`; the locality step of Lemma 2.4 holds with no
hypothesis (`coneHarmonicBallLocalityStep_holds`). At the canonical model
`ProbeMi.canonicalSLEModel ν`, `ReferenceInputs` follows from the premises `CanonicalHypotheses ν`
(`MatedCRT/Assembly/Canonical.lean`), so the certified reference model holds there, and `MainHypotheses` holds there
from `CanonicalHypotheses ν` and `OpenStepHypotheses`.

## Main statements

* `ReferenceInputs.certifiedReferenceModel`: the certified reference model `CertifiedReferenceModel ν 𝒮` of the
  counted forms from `ReferenceInputs 𝒮 ν`; `certifiedReferenceModel_canonical` at the canonical model from
  `CanonicalHypotheses ν`.
* `ReferenceHypotheses.toRemainingHypotheses`: `RemainingHypotheses 𝒮` from `ReferenceHypotheses 𝒮 ν`.
* `convergenceOfIDLA_of_referenceInputs`, `convergenceOfDivSandpile_of_referenceInputs`: Theorems 1.4 and 1.6 for
  every model from `ReferenceInputs 𝒮 ν` alone, by the counted forms `closed_1_4_quantumConeScaling_coneDimension`
  and `closed_1_6_quantumConeScaling_coneDimension` with Theorem 2.11 (`ReferenceInputs.randomWalkToLBM`); the open
  steps are not used.
* `convergenceOfIDLA_of_reference`, `convergenceOfDivSandpile_of_reference`: Theorems 1.4 and 1.6 through
  `MainHypotheses`, from `ReferenceHypotheses 𝒮 ν`.
* `mainHypotheses_canonical`: `MainHypotheses (ProbeMi.canonicalSLEModel ν)` from `CanonicalHypotheses ν` and
  `OpenStepHypotheses (ProbeMi.canonicalSLEModel ν)`.
-/

set_option autoImplicit false

open MeasureTheory

namespace MatedCRT

/-- **Lemma 2.3** (harmonic balls of the quantum cone), with no hypothesis. -/
theorem coneHarmonicBallsStmt_holds : ConeHarmonicBallsStmt :=
  closed_2_3_lp_derivedInputs FirstPass.Derived.quantumConeScalingInput_derived

/-- **Lemma 2.4** (Draft form: the harmonic balls of the cone up to the half-ball time, with the uniqueness of the
time), with no hypothesis. -/
theorem coneHarmonicBallsUpToFixedTimeStmt_holds : ConeHarmonicBallsUpToFixedTimeStmt :=
  coneHarmonicBallsUpToFixedTimeStmt_of_canonical coneCanonicalHalfBallStep_holds coneHalfBallClosureInsideStep_holds

/-- **Lemma 2.5** (Draft form: scale invariance of the cone harmonic balls up to the half-ball time), with no
hypothesis. -/
theorem coneScaleInvarianceUpToFixedTimeStmt_holds : ConeScaleInvarianceUpToFixedTimeStmt :=
  coneScaleInvarianceUpToFixedTimeStmt_of_canonical coneCanonicalHalfBallStep_holds
    coneHalfBallClosureInsideStep_holds (closed_2_5_lp_derivedInputs FirstPass.Derived.quantumConeScalingInput_derived)
    (coneRescaledHalfBallHorizonUnique_fp coneCanonicalHalfBallStep_holds coneHalfBallClosureInsideStep_holds
      (FirstPass.Derived.coneRescaledMeasureIsConeFieldInput_of_scaling
        FirstPass.Derived.quantumConeScalingInput_derived))

/-- The family of Lemma 2.4 is almost surely a measurable function of the field (`ConeFamilyAEMeasurableStep`), with
no hypothesis. -/
theorem coneFamilyAEMeasurableStep_holds : ConeFamilyAEMeasurableStep :=
  coneFamilyAEMeasurableStep_of_numbered_results coneHarmonicBallsUpToFixedTimeStmt_holds
    coneScaleInvarianceUpToFixedTimeStmt_holds FirstPass.Derived.volumeGrowthStmt_holds
    FirstPass.Derived.quantumConeScalingInput_derived
    (lqgMeasurePropertiesStmt_of_scaling FirstPass.Derived.quantumConeScalingInput_derived)

/-- **The locality step of Lemma 2.4** (`ConeHarmonicBallLocalityStep`), with no hypothesis. The event
`HasConeHarmonicBallsUpToHalfBall` of a stopped family of Lemma 2.4 has probability one both for the quantum cone
(Lemma 2.4, `coneHarmonicBallsUpToFixedTimeStmt_holds`) and for `h^ℂ - γ log |·|` (HB22, Theorem 1.1, the family
stopped when it reaches `∂B_{1/2}`: `wholePlaneHalfBallFamilyStep_of_hb`), so the set of all restrictions to `B_1` is a
measurable set with the two almost sure equivalences. -/
theorem coneHarmonicBallLocalityStep_holds : ConeHarmonicBallLocalityStep := by
  intro γ hγ hγ2
  refine ⟨Set.univ, MeasurableSet.univ, fun Ω _ P hC hcirc μ hcone => ?_,
    fun Ω _ P hC hcirc μ hP hgff hlqg => ?_⟩
  · filter_upwards [coneHarmonicBallsUpToFixedTimeStmt_holds γ hγ hγ2 Ω P hC hcirc μ hcone] with ω hω
    obtain ⟨T, hT, Λ, hΛ, hs, -⟩ := hω
    exact iff_of_true ⟨T, hT, Λ, hΛ, hs⟩ (Set.mem_univ _)
  · filter_upwards [wholePlaneHalfBallFamilyStep_of_hb _root_.HarmonicBalls.firstPass_1_1_derivedInputs43.{0}
      _root_.HarmonicBalls.Closure.closure_5_5_derivedInputs43.{0}
      _root_.HarmonicBalls.Closure.closure_5_6_derivedInputs43.{0}
      _root_.HarmonicBalls.Closure.closure_3_1_derivedInputs43.{0}
      _root_.HarmonicBalls.Closure.closure_3_2_derivedInputs43.{0}
      _root_.HarmonicBalls.Closure.closure_3_3_derivedInputs43.{0}
      _root_.HarmonicBalls.Closure.closure_3_4_derivedInputs43.{0}
      _root_.HarmonicBalls.Closure.closure_3_5_derivedInputs43.{0}
      _root_.HarmonicBalls.Closure.closure_5_2_derivedInputs43.{0}
      _root_.HarmonicBalls.Closure.closure_5_3_derivedInputs43.{0}
      _root_.HarmonicBalls.Closure.closure_5_8_derivedInputs43.{0} γ hγ hγ2 Ω P hC hcirc μ hP hgff hlqg] with ω hω
    exact iff_of_true hω (Set.mem_univ _)

/-- The four open steps: four fields of `MainHypotheses 𝒮`, with the same names and types. The locality step of
Lemma 2.4 is proved (`coneHarmonicBallLocalityStep_holds`), and so are the steps of Proposition 5.1: the geometry and
margin steps for every model, the pole step `stoppedSurplusPole` and the layer step `stoppedLayerPotential` from
`ReferenceInputs` (`ReferenceInputs.stoppedSurplusPole`, `ReferenceInputs.stoppedLayerPotential`). -/
structure OpenStepHypotheses (𝒮 : SpaceFillingSLEModel) : Prop where
  /-- Lemmas 2.4, 2.5, Theorems 1.4, 1.6: strict growth of the cone harmonic balls (`T' = T`, not in the
  paper). -/
  coneHarmonicBallStrictGrowth : ConeHarmonicBallStrictGrowthStep
  /-- Lemma 2.5, Theorems 1.4, 1.6: the half-ball family is a functional of the field. -/
  coneHalfBallFamilyFunctional : ConeHalfBallFamilyFunctionalStep
  /-- Lemma 4.6 (corrected route): local compactness of the odometers. -/
  odometerLocalCompactnessCorrected : OdometerLocalCompactnessCorrectedStep 𝒮
  /-- Lemma 4.6 (corrected route): boundary upgrade. -/
  odometerBoundaryUpgradeCorrected : OdometerBoundaryUpgradeCorrectedStep 𝒮

/-- A model `𝒮` with normalized space-filling SLE law `ν`, the SLE closure inputs, valid environments on `ℝ`, the
uniform-start invariance principle and the chart forms of Berestycki-Gwynne, Lemmas 7.20 and 7.21. -/
structure ReferenceInputs (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode) : Prop where
  /-- `𝒮` has the normalized space-filling SLE law `ν`. -/
  law : HasNormalizedSLELaw 𝒮 ν
  /-- The SLE closure inputs of the model (`SLEModelClosureInput`). -/
  sleModelClosure : SLEModelClosureInput 𝒮
  /-- The uniform-start invariance principle for the walk on the mated-CRT map (`GMS21UniformStartInput`). -/
  uniformStart : GMS21UniformStartInput 𝒮
  /-- Valid environments of `𝒮` on `ℝ` for every `0 < γ < 2`. -/
  referenceEnvironments : HasReferenceEnvironments 𝒮
  /-- The chart forms of Berestycki-Gwynne, Lemmas 7.20 and 7.21. -/
  chartField : BG20ChartFieldInput 𝒮

/-- `ReferenceInputs 𝒮 ν` and the open steps. -/
structure ReferenceHypotheses (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode) : Prop
    extends ReferenceInputs 𝒮 ν where
  /-- The open steps. -/
  steps : OpenStepHypotheses 𝒮

namespace ReferenceInputs

variable {𝒮 : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}

/-- **Lemma 2.14** (Berestycki-Gwynne, Lemma 5.4) from `ReferenceInputs`. -/
theorem greenKernelUpperBound (H : ReferenceInputs 𝒮 ν) : GreenKernelUpperBoundStmt 𝒮 :=
  have hU := exists_matingRigidLEOn_full_derived
  FirstPass.Derived.greenKernelUpperBoundStmt_of_reference H.law H.referenceEnvironments hU.choose_spec.1
    hU.choose_spec.2

/-- **Lemma 2.16** (Berestycki-Gwynne, Lemma 4.4) from `ReferenceInputs`. -/
theorem greenKernelLowerBound (H : ReferenceInputs 𝒮 ν) : GreenKernelLowerBoundStmt 𝒮 :=
  have hU := exists_matingRigidLEOn_full_derived
  FirstPass.Derived.greenKernelLowerBoundStmt_of_reference H.law H.law H.referenceEnvironments hU.choose_spec.1
    hU.choose_spec.2

/-- **Theorem 2.11** (Berestycki-Gwynne, Theorem 1.2) from `ReferenceInputs`. -/
theorem randomWalkToLBM (H : ReferenceInputs 𝒮 ν) : RandomWalkToLBMStmt 𝒮 :=
  randomWalkToLBMStmt_of_markovLimit_bg20ChartField H.law H.sleModelClosure H.uniformStart H.referenceEnvironments
    H.chartField

/-- **Lemma 2.18** from `ReferenceInputs`, through Lemma 2.14. -/
theorem exitTimeUpperBound (H : ReferenceInputs 𝒮 ν) : ExitTimeUpperBoundStmt 𝒮 :=
  FirstPass.Derived.exitTimeUpperBoundStmt_of_greenKernelUpper H.greenKernelUpperBound

/-- **The scaling of the expected exit time** (Berestycki-Gwynne (1.8)) from `ReferenceInputs`. -/
theorem mepsScaling (H : ReferenceInputs 𝒮 ν) : MepsScalingInput 𝒮 :=
  mepsScalingInput_of_lower H.exitTimeUpperBound (boundedExitTimeRV_of_steps FirstPass.Derived.volumeGrowthStmt_holds)
    (FirstPass.Derived.mεCdf_lower_of_lemma69 H.greenKernelUpperBound H.greenKernelLowerBound
      (ExitTimeLowerTail.exitTimeLowerTail_of_uniformStart H.uniformStart))

/-- **The corrected Lemma 3.2** (GMS19 Theorem 3.9) from `ReferenceInputs`. -/
theorem discreteHolderContinuityCorrected (H : ReferenceInputs 𝒮 ν) :
    FrozenDiscreteHolderContinuityCorrected 𝒮 :=
  have hU := exists_matingRigidLEOn_full_derived
  FirstPass.Derived.frozenDiscreteHolderContinuityCorrected_of_reference H.law H.referenceEnvironments
    (fun γ hγ0 hγ2 => ⟨hU.choose, hU.choose_spec.1 γ hγ0 hγ2, hU.choose_spec.2⟩)
    (FirstPass.Derived.cellSizeEstimateStmt_holds 𝒮)

/-- **The certified reference model** (`CertifiedReferenceModel ν 𝒮`, the bundle of cited inputs of the counted
forms of docs/campaign/COUNTED.md) from `ReferenceInputs`: its core by
`FirstPass.Derived.CertifiedReferenceModelCore.of_runningMinTail_law_degree_derived`, with the occupation identity of
Appendix B (`KilledOccupation.frozenLBMGreenOccupationRescaled_holds`), Lemma 2.15 and the rescaled environment, and
the truncated quenched laws by `certifiedReferenceModel_of_core`. -/
theorem certifiedReferenceModel (H : ReferenceInputs 𝒮 ν) : CertifiedReferenceModel ν 𝒮 :=
  certifiedReferenceModel_of_core
    (FirstPass.Derived.CertifiedReferenceModelCore.of_runningMinTail_law_degree_derived H.law H.sleModelClosure
      H.mepsScaling (KilledOccupation.frozenLBMGreenOccupationRescaled_holds 𝒮) H.referenceEnvironments
      H.randomWalkToLBM H.greenKernelUpperBound H.greenKernelLowerBound H.discreteHolderContinuityCorrected
      (greenFunctionCrudeBoundStmt_holds 𝒮)
      (coneEnvironmentScalingUnderSLE_of_scaling 𝒮 FirstPass.Derived.quantumConeScalingInput_derived
        H.sleModelClosure.1 H.sleModelClosure.2.1 H.sleModelClosure.2.2))
    frozenBrownianOutwardExcursionAtExit_holds

/-- **The Draft Lemma 3.5** from `ReferenceInputs`: the corrected Lemma 3.5 of the certified reference model
(`closed_3_5_lp_derivedInputs`) and `FirstPass35Bridge.discreteDirichletProblem_of_corrected`. -/
theorem discreteDirichletProblem (H : ReferenceInputs 𝒮 ν) : DiscreteDirichletProblemStmt 𝒮 :=
  FirstPass35Bridge.discreteDirichletProblem_of_corrected H.certifiedReferenceModel.cellSizeEstimate
    closed_2_13_cellRewire (closed_3_5_lp_derivedInputs 𝒮 ν H.certifiedReferenceModel)

/-- **Lemma 4.6, prepared form** (`SubsequentialConvergencePreparedStmt`) from `ReferenceInputs`: the counted form
`firstPass_4_6_h35c_derivedInputs` with its inputs from the certified reference model and Lemmas 3.5 (corrected)
and 3.7 (`closed_3_5_lp_derivedInputs`, `closed_3_7_lp_derivedInputs`). -/
theorem subsequentialConvergencePrepared (H : ReferenceInputs 𝒮 ν) : SubsequentialConvergencePreparedStmt 𝒮 :=
  firstPass_4_6_h35c_derivedInputs H.certifiedReferenceModel.mepsScaling H.certifiedReferenceModel.exitTimeUpperBound
    H.certifiedReferenceModel.frozenDiscreteHolderContinuityCorrected H.certifiedReferenceModel.cellSizeEstimate
    (closed_3_5_lp_derivedInputs 𝒮 ν H.certifiedReferenceModel) (closed_3_7_lp_derivedInputs 𝒮 ν H.certifiedReferenceModel)

/-- **The one-sided boundary continuity of Lemma 3.6** (`FrozenOneSidedBoundaryContinuityFlooredUniform`: GMS19
(3.31) as proved on p. 32, with the floor `ε ^ β` on the boundary distance and `β` chosen before the radius) from
`ReferenceInputs`: `FirstPass.Derived.frozenOneSidedBoundaryContinuityFlooredUniform_of_reference`, with Lemma 3.11
in the reference environments and the full one-sided mating-rigid set `exists_matingRigidLEOn_full_derived`. -/
theorem oneSidedBoundaryContinuity (H : ReferenceInputs 𝒮 ν) :
    FirstPass36.FrozenOneSidedBoundaryContinuityFlooredUniform 𝒮 :=
  FirstPass.Derived.frozenOneSidedBoundaryContinuityFlooredUniform_of_reference H.law H.referenceEnvironments
    exists_matingRigidLEOn_full_derived

/-- **Lemma 3.6** (corrected harmonic convergence and its same-walk annealed form) from `ReferenceInputs`: the
counted form `closed_3_6_lp_uniform_derivedInputs` with the certified reference model and the one-sided boundary
continuity. -/
theorem correctedHarmonicConvergence (H : ReferenceInputs 𝒮 ν) :
    CorrectedHarmonicConvergenceStmt 𝒮 ∧ FirstPass36.CorrectedHarmonicSameWalkAnnealedStmt 𝒮 :=
  closed_3_6_lp_uniform_derivedInputs 𝒮 ν H.certifiedReferenceModel H.oneSidedBoundaryContinuity

/-- **The pole step of Proposition 5.1** (`StoppedSurplusPoleStep`) from
`ReferenceInputs`: `StoppedInterior.stoppedSurplusPole_of_steps` with the strict obstacle gap, the geometry and margin
steps (proved for every model), the scaling of the expected exit time, Theorem 4.1, Lemma 3.3 and Lemmas 2.16 and
2.18. -/
theorem stoppedSurplusPole (H : ReferenceInputs 𝒮 ν) : StoppedInterior.StoppedSurplusPoleStep 𝒮 :=
  StoppedInterior.stoppedSurplusPole_of_steps 𝒮 (harmonicBallStrictObstacleGapStep_holds 𝒮)
    (StoppedGeometry.stoppedInteriorGeometryStep_holds 𝒮) (StoppedCode.stoppedInteriorMeasurableStep_holds 𝒮)
    H.mepsScaling (closed_4_1_lp_derivedInputs ν H.certifiedReferenceModel)
    (closed_3_3_ownBinders_derivedInputs 𝒮 ν H.certifiedReferenceModel) H.greenKernelLowerBound
    H.exitTimeUpperBound

/-- **The number of missing sites of Proposition 5.1** (`StoppedMissingSitesStep`) from `ReferenceInputs`: `StoppedMissing.stoppedMissingSites_of_innerBound` with Proposition 4.2 in the form
`DiscreteClusterInnerBoundStep` (`discreteClusterInnerBound_prop42`: Theorem 4.1, Lemmas 2.3, 2.4, 2.7, 2.8, 3.3, the
measurability of the family of Lemma 2.4 and the strict obstacle gap). -/
theorem stoppedMissingSites (H : ReferenceInputs 𝒮 ν) : StoppedMissingSitesStep 𝒮 :=
  StoppedMissing.stoppedMissingSites_of_innerBound 𝒮
    (discreteClusterInnerBound_prop42 𝒮 (closed_4_1_lp_derivedInputs ν H.certifiedReferenceModel)
      coneHarmonicBallsStmt_holds coneHarmonicBallsUpToFixedTimeStmt_holds FirstPass.Derived.volumeGrowthStmt_holds
      (FirstPass.Derived.cellSizeEstimateStmt_holds 𝒮)
      (closed_3_3_ownBinders_derivedInputs 𝒮 ν H.certifiedReferenceModel) coneFamilyAEMeasurableStep_holds
      (harmonicBallStrictObstacleGapStep_holds 𝒮))

/-- **The layer step of Proposition 5.1** (`StoppedLayerPotentialStep`) from
`ReferenceInputs`: `stoppedLayerPotential_of_missingSites` with Lemma 2.14 and the number of missing sites. -/
theorem stoppedLayerPotential (H : ReferenceInputs 𝒮 ν) : StoppedLayerPotentialStep 𝒮 :=
  stoppedLayerPotential_of_missingSites 𝒮 H.greenKernelUpperBound H.stoppedMissingSites

end ReferenceInputs

/-- `RemainingHypotheses 𝒮` from `ReferenceHypotheses 𝒮 ν`: the five cited fields are proved from the law, the
closure inputs, the reference environments, the uniform-start input and the chart forms, and Lemma 3.4 and the
lower surplus estimate of Lemma 5.3 from them. -/
theorem ReferenceHypotheses.toRemainingHypotheses {𝒮 : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (H : ReferenceHypotheses 𝒮 ν) : RemainingHypotheses 𝒮 :=
  { randomWalkToLBM := H.toReferenceInputs.randomWalkToLBM
    greenKernelUpperBound := H.toReferenceInputs.greenKernelUpperBound
    greenKernelLowerBound := H.toReferenceInputs.greenKernelLowerBound
    mepsScaling := H.toReferenceInputs.mepsScaling
    sleModelClosure := H.sleModelClosure
    discreteHolderContinuityCorrected := H.toReferenceInputs.discreteHolderContinuityCorrected
    coneHarmonicBallLocality := coneHarmonicBallLocalityStep_holds
    coneHarmonicBallStrictGrowth := H.steps.coneHarmonicBallStrictGrowth
    coneHalfBallFamilyFunctional := H.steps.coneHalfBallFamilyFunctional
    dirichletInterior := dirichletInteriorStep_of_draft H.toReferenceInputs.discreteDirichletProblem
      FirstPass.Derived.volumeGrowthStmt_holds
    dirichletBoundary := dirichletBoundaryStep_of_draft H.toReferenceInputs.discreteDirichletProblem
      FirstPass.Derived.volumeGrowthStmt_holds
    odometerLocalCompactnessCorrected := H.steps.odometerLocalCompactnessCorrected
    odometerBoundaryUpgradeCorrected := H.steps.odometerBoundaryUpgradeCorrected
    odometerMeasurableSelection :=
      odometerMeasurableSelectionStep_of_prepared H.toReferenceInputs.subsequentialConvergencePrepared
    stoppedSurplusPole := H.toReferenceInputs.stoppedSurplusPole
    stoppedInteriorGeometry := StoppedGeometry.stoppedInteriorGeometryStep_holds 𝒮
    stoppedInteriorMeasurable := StoppedCode.stoppedInteriorMeasurableStep_holds 𝒮
    stoppedLayerPotential := H.toReferenceInputs.stoppedLayerPotential
    meanValueSurplusLower := meanValueSurplusLowerStep_of_meps H.toReferenceInputs.mepsScaling
    integralConvergenceGreenFunction := integralConvergenceGreenFunction_of_walk H.toReferenceInputs.randomWalkToLBM
      H.toReferenceInputs.exitTimeUpperBound H.toReferenceInputs.mepsScaling }

/-- **Theorem 1.4** (convergence of IDLA) for every model, from `ReferenceHypotheses 𝒮 ν`. -/
theorem convergenceOfIDLA_of_reference (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode)
    (H : ReferenceHypotheses 𝒮 ν) : ConvergenceOfIDLAStmt 𝒮 :=
  convergenceOfIDLA_of_remaining 𝒮 H.toRemainingHypotheses

/-- **Theorem 1.6** (convergence of the divisible sandpile) for every model, from `ReferenceHypotheses 𝒮 ν`. -/
theorem convergenceOfDivSandpile_of_reference (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode)
    (H : ReferenceHypotheses 𝒮 ν) : ConvergenceOfDivSandpileStmt 𝒮 :=
  convergenceOfDivSandpile_of_remaining 𝒮 H.toRemainingHypotheses

/-- **Theorem 1.4** (convergence of IDLA) for every model, from `ReferenceInputs 𝒮 ν` alone: the counted form
`closed_1_4_quantumConeScaling_coneDimension` with Theorem 2.11 from `ReferenceInputs.randomWalkToLBM`. The open
steps `OpenStepHypotheses 𝒮` are not used. -/
theorem convergenceOfIDLA_of_referenceInputs (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode)
    (H : ReferenceInputs 𝒮 ν) : ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_quantumConeScaling_coneDimension ν H.law H.sleModelClosure H.uniformStart H.referenceEnvironments
    H.randomWalkToLBM

/-- **Theorem 1.6** (convergence of the divisible sandpile) for every model, from `ReferenceInputs 𝒮 ν` alone: the
counted form `closed_1_6_quantumConeScaling_coneDimension` with Theorem 2.11 from `ReferenceInputs.randomWalkToLBM`.
The open steps `OpenStepHypotheses 𝒮` are not used. -/
theorem convergenceOfDivSandpile_of_referenceInputs (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode)
    (H : ReferenceInputs 𝒮 ν) : ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_quantumConeScaling_coneDimension ν H.law H.sleModelClosure H.uniformStart H.referenceEnvironments
    H.randomWalkToLBM

/-- `ReferenceInputs` at the canonical model from `CanonicalHypotheses ν`: the law and the closure inputs from the
mating-of-trees couplings, the reference environments from the couplings and the dyadic Liouville clocks, and the
uniform-start input from the couplings and `tutteLP`. -/
theorem referenceInputs_canonical (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) :
    ReferenceInputs (ProbeMi.canonicalSLEModel ν) ν :=
  have hfix := Sec1.wholePlane_fixedStart_uniformCauchy_of_localLimit
    FirstPass.Derived.gaussianClock_localLimit_of_lt_two
  { law := FirstPass.Derived.hasNormalizedSLELaw_canonicalSLEModel_of_coupling H.matingOfTreesCoupling
    sleModelClosure := FirstPass.Derived.sleModelClosureInput_canonicalSLEModel_of_coupling H.matingOfTreesCoupling
    uniformStart := gms21UniformStartInput_of_selectedLP_reference
      (FirstPass.Derived.hasNormalizedSLELaw_canonicalSLEModel_of_coupling H.matingOfTreesCoupling)
      (FirstPass.Derived.sleModelClosureInput_canonicalSLEModel_of_coupling H.matingOfTreesCoupling) H.tutteLP
    referenceEnvironments := Sec1.hasReferenceEnvironments_canonical_of_coupling_wholePlane_fixedStart ν
      H.matingOfTreesCoupling hfix
      (Sec1.wholePlane_fixedStart_strictMono_of_oneStart FirstPass.Derived.gaussianClock_oneStart hfix)
    chartField := H.chartField }

/-- `ReferenceHypotheses` at the canonical model from `CanonicalHypotheses ν` and the open steps. -/
theorem referenceHypotheses_canonical (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν)
    (hS : OpenStepHypotheses (ProbeMi.canonicalSLEModel ν)) :
    ReferenceHypotheses (ProbeMi.canonicalSLEModel ν) ν :=
  { referenceInputs_canonical ν H with steps := hS }

/-- **The certified reference model at the canonical model** from `CanonicalHypotheses ν`. -/
theorem certifiedReferenceModel_canonical (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) :
    CertifiedReferenceModel ν (ProbeMi.canonicalSLEModel ν) :=
  (referenceInputs_canonical ν H).certifiedReferenceModel

/-- **The hypotheses of the main theorems at the canonical model**: `MainHypotheses (ProbeMi.canonicalSLEModel ν)`
from `CanonicalHypotheses ν` and the open steps. -/
theorem mainHypotheses_canonical (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν)
    (hS : OpenStepHypotheses (ProbeMi.canonicalSLEModel ν)) : MainHypotheses (ProbeMi.canonicalSLEModel ν) :=
  (referenceHypotheses_canonical ν H hS).toRemainingHypotheses.toMainHypotheses

end MatedCRT
