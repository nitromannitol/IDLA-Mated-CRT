import MatedCRT.FirstPass.S5c
import MatedCRT.FirstPass.S4d.StrictGapReduction
import MatedCRT.FirstPass.S4d.DeterministicComparison
import MatedCRT.FirstPass.S4d.FixedTimeUnion
import MatedCRT.FirstPass.S4d.FixedTimeFinal
import MatedCRT.FirstPass.S2g.HalfBallGate

/-!
# FIRST PASS, Proposition 4.2 (prop:div-sandpile-lower-bound): assembly with the cone family

`firstPass_4_2` (FirstPass/S5c.lean) assembles `firstPass_4_1` (Theorem 4.1), the cited
inputs and `divSandpileLowerBound_final` (Proofs/Sec4/DivSandpileLowerBound/Final.lean). Its cone hypotheses enter only
through the measurability step `ConeFamilyAEMeasurableStep`, which `coneFamilyAEMeasurable_proved` (FirstPass/S2j.lean) discharges from explicit cone hypotheses.

* `firstPass_4_2_of_coneFamilyStep`: the assembly with the single hypothesis `hfam : ConeFamilyAEMeasurableStep`.
* `firstPass_4_2_assembled`: the same conclusion, with `hfam` discharged by `coneFamilyAEMeasurable_proved`.

Open NEW inputs, kept as explicit hypotheses (not proved here):
* `hgap : HarmonicBallStrictObstacleGapStep 𝒮` (Proofs/Sec4/DivSandpileLowerBound/Final.lean:32), the strict obstacle gap.
  Its printed proof, `eq:strictly-above-in-interior` (paper/idla_mated_crt-corrected.tex, label at line 1913, "there exists
  s > 0 by continuity"), does not establish strict positivity on the interior of the closure of the positivity set (`StrictGapCounterexample.lean`); the missing ingredient is item (2) of the gap audit.
* `hcan : ConeCanonicalHalfBallStep` (FirstPass/S2g.lean:82) and `hcl : ConeHalfBallClosureInsideStep`
  (Proofs/Sec2/ConeFamilyMeasurable/StoppedClosure.lean:18, documented there as not stated in the paper); they are used
  only by `firstPass_4_2_assembled`.

Both theorems are conditional on `hgap`. The full hypothesis lists are in the docstrings of the two theorems.
-/

namespace MatedCRT

/-- **Proposition 4.2 (first pass), from the cone family step.** Hypotheses, in order:
* cited inputs (as in `firstPass_4_2`, FirstPass/S5c.lean): `hm`, `h210`, `h34`, `h214`, `h28`, `h35`, `h218`, `h27`,
  `hH`, `hcone`, `h23`, `h24`, `h33`;
* the open NEW input `hgap : HarmonicBallStrictObstacleGapStep 𝒮` (Final.lean:32);
* the cone family measurability step `hfam : ConeFamilyAEMeasurableStep` (the Theorem 2.3 measurability, Steps/Sec2).
Conclusion: `DivSandpileLowerBoundStmt 𝒮`. -/
theorem firstPass_4_2_of_coneFamilyStep {𝒮 : SpaceFillingSLEModel}
    -- cited inputs
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeEnvironmentScaling 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    -- open NEW input
    (hgap : HarmonicBallStrictObstacleGapStep 𝒮)
    -- cone family measurability
    (hfam : ConeFamilyAEMeasurableStep) :
    DivSandpileLowerBoundStmt 𝒮 :=
  divSandpileLowerBound_final 𝒮 (firstPass_4_1 hm h210 h34 h214 h28 h35 h218 h27 hH hcone) h23 h24 h27 h28 h33 hfam hgap

/-- **Proposition 4.2 (first pass), from the two strict-gap steps.** Same conclusion as
`firstPass_4_2_of_coneFamilyStep`, with the open NEW input `hgap` replaced by its two named components
 (`FirstPass/S4d/StrictGapReduction.lean`): `hdet` (deterministic comparison, Section 2) and `hnj`
(fixed-time union, Sections 4-5). Hypotheses, in order: the cited inputs as in `firstPass_4_2_of_coneFamilyStep`;
the open NEW inputs `hdet`, `hnj`; the cone family measurability `hfam`. -/
theorem firstPass_4_2_of_strictGapSteps {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeEnvironmentScaling 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (hdet : StrictGapDeterministicComparisonStep) (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hfam : ConeFamilyAEMeasurableStep) :
    DivSandpileLowerBoundStmt 𝒮 :=
  firstPass_4_2_of_coneFamilyStep hm h210 h34 h214 h28 h35 h218 h27 hH hcone h23 h24 h33
    (harmonicBallStrictObstacleGapStep_of_steps 𝒮 hdet hnj) hfam

/-- **Proposition 4.2 (first pass), assembled.** Same conclusion as
`firstPass_4_2_of_coneFamilyStep`, with `hfam` discharged by `coneFamilyAEMeasurable_proved` (FirstPass/S2j.lean:28).
Hypotheses, in order:
* cited inputs: as in `firstPass_4_2_of_coneFamilyStep`;
* the open NEW input `hgap` (Final.lean:32);
* open NEW cone steps: `hcan : ConeCanonicalHalfBallStep`, `hcl : ConeHalfBallClosureInsideStep`;
* frozen cone externals: `hE1 : ConeCircleLawUniqueStep` (Frozen/S2i.lean:24), `hE2 : ConeReferenceExistsStep`
  (Frozen/S2i.lean:40);
* `hscale : QuantumConeScalingInput` (External/QuantumCone.lean:19) and `h22 : LQGMeasurePropertiesStmt`
  (Draft/Section2.lean:39).
Conclusion: `DivSandpileLowerBoundStmt 𝒮`. -/
theorem firstPass_4_2_assembled {𝒮 : SpaceFillingSLEModel}
    -- cited inputs
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeEnvironmentScaling 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    -- open NEW input
    (hgap : HarmonicBallStrictObstacleGapStep 𝒮)
    -- open NEW cone steps
    (hcan : ConeCanonicalHalfBallStep) (hcl : ConeHalfBallClosureInsideStep)
    -- frozen cone externals, quantum cone scaling, LQG measure property
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt) :
    DivSandpileLowerBoundStmt 𝒮 :=
  firstPass_4_2_of_coneFamilyStep hm h210 h34 h214 h28 h35 h218 h27 hH hcone h23 h24 h33 hgap
    (coneFamilyAEMeasurable_proved hcan hcl h27 hE1 hE2 hscale h22)

/-- **Proposition 4.2 (first pass), with the deterministic comparison discharged.** Same
conclusion as `firstPass_4_2_of_strictGapSteps`, with `hdet` proved by `strictGapDeterministicComparison_of_frozen`
(S4d/DeterministicComparison.lean) from the explicit potential-theoretic inputs `hG` (HB `GreenFunctionBallStmt`, Draft),
`hpc` (`FrozenPunctureConnected`, Frozen/S4d.lean), `hsmp` (`FPStrongMinimumPrinciple`, Frozen/S5c.lean), `hwmp`
(`FrozenSuperharmonicMinimumPrinciple`) and `hpole` (`FrozenGreenDiscPole`, Frozen/S2g.lean). Open NEW inputs left:
`hnj : StrictGapFixedTimeUnionStep 𝒮` (Sections 4-5) and the cone measurability `hfam`. The cited inputs are as in
`firstPass_4_2_of_coneFamilyStep`. -/
theorem firstPass_4_2_of_frozen_strictGap {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeEnvironmentScaling 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (hG : _root_.HarmonicBalls.GreenFunctionBallStmt) (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple) (hwmp : FrozenSuperharmonicMinimumPrinciple)
    (hpole : FrozenGreenDiscPole)
    (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hfam : ConeFamilyAEMeasurableStep) :
    DivSandpileLowerBoundStmt 𝒮 :=
  firstPass_4_2_of_strictGapSteps hm h210 h34 h214 h28 h35 h218 h27 hH hcone h23 h24 h33
    (strictGapDeterministicComparison_of_frozen hG hpc hsmp hwmp hpole) hnj hfam

/-- **Proposition 4.2 (first pass), final assembly.** The conclusion `DivSandpileLowerBoundStmt 𝒮`
(Draft Proposition 4.2, `Draft/Section4.lean:50`) with every route-level input made explicit. The name `firstPass_4_2`
is taken by FirstPass/S5c.lean (with `hgap`), so this is `firstPass_4_2_final`.
Hypotheses, in order:
* cited inputs, as in `firstPass_4_2_of_coneFamilyStep`: `hm`, `h210`, `h34`, `h214`, `h28`, `h35`, `h218`, `h27`, `hH`,
  `hcone`, `h23`, `h24`, `h33`;
* deterministic comparison, discharged by `strictGapDeterministicComparison_of_frozen` from the explicit inputs
  `hG` (`HarmonicBalls.GreenFunctionBallStmt`, Draft), `hpc` (`FrozenPunctureConnected`, Frozen/S4d.lean),
  `hsmp` (`FPStrongMinimumPrinciple`, Frozen/S5c.lean), `hwmp` (`FrozenSuperharmonicMinimumPrinciple`, Frozen/S2g.lean),
  `hpole` (`FrozenGreenDiscPole`, Frozen/S2g.lean);
* open NEW input `hnj : StrictGapFixedTimeUnionStep 𝒮` (fixed-time union; the measurability
  input is not yet available, see S4d/StrictGapReduction.lean);
* open NEW cone steps `hcan : ConeCanonicalHalfBallStep` (FirstPass/S2g.lean:82) and
  `hcl : ConeHalfBallClosureInsideStep` (Proofs/Sec2/ConeFamilyMeasurable/StoppedClosure.lean:18);
* frozen cone externals `hE1 : ConeCircleLawUniqueStep` (Frozen/S2i.lean:24), `hE2 : ConeReferenceExistsStep`
  (Frozen/S2i.lean:40), `hscale : QuantumConeScalingInput` (External/QuantumCone.lean:19), and
  `h22 : LQGMeasurePropertiesStmt` (Draft/Section2.lean:39).
The cone family measurability `hfam : ConeFamilyAEMeasurableStep` is discharged by `coneFamilyAEMeasurable_proved`
(FirstPass/S2j.lean:28). -/
theorem firstPass_4_2_final {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeEnvironmentScaling 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (hG : _root_.HarmonicBalls.GreenFunctionBallStmt) (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple) (hwmp : FrozenSuperharmonicMinimumPrinciple)
    (hpole : FrozenGreenDiscPole)
    (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hcan : ConeCanonicalHalfBallStep) (hcl : ConeHalfBallClosureInsideStep)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt) :
    DivSandpileLowerBoundStmt 𝒮 :=
  firstPass_4_2_of_frozen_strictGap hm h210 h34 h214 h28 h35 h218 h27 hH hcone h23 h24 h33 hG hpc hsmp hwmp hpole hnj
    (coneFamilyAEMeasurable_proved hcan hcl h27 hE1 hE2 hscale h22)


/-- **Proposition 4.2 with the fixed-time union discharged.** The hypothesis `hnj` of
`firstPass_4_2_final` is `strictGapFixedTimeUnion_of_steps` (S4d/FixedTimeUnion.lean), whose inputs are the cone scaling
law `hScaleInv` (Lemma 2.6, `ConeScaleInvarianceStmt`), the explicit OPEN steps `hB2` (`ConeGlobalFamilyPairAEMeasurableStep`)
and `hB2R` (`ConeRescaledPairAEMeasurableStep`), and the frozen positivity `hFCS : FrozenConeScalingLaw 𝒮`
(Frozen/S4S6c.lean). The other hypotheses are those of `firstPass_4_2_final`, in the same order. -/
theorem firstPass_4_2_of_scale_inputs {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeEnvironmentScaling 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (hG : _root_.HarmonicBalls.GreenFunctionBallStmt) (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple) (hwmp : FrozenSuperharmonicMinimumPrinciple)
    (hpole : FrozenGreenDiscPole)
    (hScaleInv : ConeScaleInvarianceStmt) (hB2 : ConeGlobalFamilyPairAEMeasurableStep)
    (hB2R : ConeRescaledPairAEMeasurableStep) (hFCS : FrozenConeScalingLaw 𝒮)
    (hcan : ConeCanonicalHalfBallStep) (hcl : ConeHalfBallClosureInsideStep)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt) :
    DivSandpileLowerBoundStmt 𝒮 :=
  firstPass_4_2_final hm h210 h34 h214 h28 h35 h218 h27 hH hcone h23 h24 h33 hG hpc hsmp hwmp hpole
    (strictGapFixedTimeUnion_of_steps 𝒮 hScaleInv hB2 hB2R hFCS) hcan hcl hE1 hE2 hscale h22


/-- **Proposition 4.2 with the fixed-time union from the dependencies.** This supersedes
`firstPass_4_2_of_scale_inputs`: the explicit measurability steps `hB2`, `hB2R` and the positivity input `hFCS` are no
longer hypotheses. They are proved (`coneGlobalFamilyAEMeasurable_of_stopped`, `coneRescaledGlobalFamilyAEMeasurable_of_stopped`,
S4d/GlobalMeasurable.lean and S4d/RescaledMeasurable.lean), and the positivity of the cone scale radii comes from `hscale`
(`coneScaleRadiusPosStep_of_input`). The paper inputs now are `h24` (Lemma 2.4), `h25` (Lemma 2.5, corrected.tex:548), and
`hScaleInv` (Lemma 2.6, corrected.tex:597). The stopped measurability `hfam` is `coneFamilyAEMeasurable_proved`
(open NEW steps `hcan`, `hcl` remain explicit). -/
theorem firstPass_4_2_of_fixed_time_steps {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeEnvironmentScaling 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (h25 : ConeScaleInvarianceUpToFixedTimeStmt) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (hG : _root_.HarmonicBalls.GreenFunctionBallStmt) (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple) (hwmp : FrozenSuperharmonicMinimumPrinciple)
    (hpole : FrozenGreenDiscPole)
    (hScaleInv : ConeScaleInvarianceStmt)
    (hcan : ConeCanonicalHalfBallStep) (hcl : ConeHalfBallClosureInsideStep)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt) :
    DivSandpileLowerBoundStmt 𝒮 :=
  firstPass_4_2_final hm h210 h34 h214 h28 h35 h218 h27 hH hcone h23 h24 h33 hG hpc hsmp hwmp hpole
    (strictGapFixedTimeUnionStep_of_steps 𝒮 h24 h25
      (coneFamilyAEMeasurable_proved hcan hcl h27 hE1 hE2 hscale h22) hScaleInv hscale)
    hcan hcl hE1 hE2 hscale h22

open _root_.HarmonicBalls in
/-- **Prop 4.2 with the canonical half-ball gate discharged.** `ConeCanonicalHalfBallStep`
is no longer a hypothesis: it is `coneCanonicalHalfBallStep_of_draft` (`FirstPass/S2g/HalfBallGate.lean`), applied to
its Draft statements and frozen inputs. The gate's minimum principle, Green ball and pole inputs are `hwmp`, `hG`, `hpole`.
Still explicit: the closure step `hcl` (`ConeHalfBallClosureInsideStep`; route B, `coneHalfBallClosureInsideStep_corrected`,
reduces it to the open `WholePlaneLQGModelStep` and `ConeWholePlaneFieldLawStep`), the scale invariance Lemma 2.6 `hScaleInv`,
the frozen cone externals `hE1`, `hE2` and the quantum cone scaling inputs. Statement of Prop 4.2 unchanged. -/
theorem firstPass_4_2_of_halfball_gate {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeEnvironmentScaling 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (h25 : ConeScaleInvarianceUpToFixedTimeStmt) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (hG : _root_.HarmonicBalls.GreenFunctionBallStmt) (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple) (hwmp : FrozenSuperharmonicMinimumPrinciple)
    (hpole : FrozenGreenDiscPole)
    (hScaleInv : ConeScaleInvarianceStmt)
    (hU : FrozenUniversalMeasurabilityOfAnalytic) (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hstd : FrozenConeLogLocalCodeLawStd) (hCentre : FrozenGreenBallCentre)
    (hOpen : ClusterOpenLaplacianStmt.{0}) (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0}) (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0}) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0}) (hconf : FrozenHBInitialConfinement)
    (hcl : ConeHalfBallClosureInsideStep)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt) :
    DivSandpileLowerBoundStmt 𝒮 :=
  firstPass_4_2_of_fixed_time_steps hm h210 h34 h214 h28 h35 h218 h27 hH hcone h23 h24 h25 h33 hG hpc hsmp hwmp hpole
    hScaleInv
    (coneCanonicalHalfBallStep_of_draft hU hmeasT hstd hwmp hCentre hG hpole hOpen hSup hCons hMono hCompat hBdry
      hExist hThm11 hProp56 hconf)
    hcl hE1 hE2 hscale h22

end MatedCRT
