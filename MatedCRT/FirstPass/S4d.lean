import MatedCRT.FirstPass.S5c
import MatedCRT.FirstPass.S4d.StrictGapReduction
import MatedCRT.FirstPass.S4d.DeterministicComparison
import MatedCRT.FirstPass.S4d.FixedTimeUnion

/-!
# FIRST PASS, Proposition 4.2 (prop:div-sandpile-lower-bound): assembly with the cone family (q4)

Task fp-S4d-4-2-assembly. `firstPass_4_2` (FirstPass/S5c.lean, q3) assembles `firstPass_4_1` (Theorem 4.1), the cited
inputs and `divSandpileLowerBound_final` (Proofs/Sec4/DivSandpileLowerBound/Final.lean). Its cone hypotheses enter only
through the measurability step `ConeFamilyAEMeasurableStep`, which `coneFamilyAEMeasurable_proved` (FirstPass/S2j.lean,
q4, commit 7b51af3) discharges from explicit cone hypotheses.

* `firstPass_4_2_of_coneFamilyStep`: the assembly with the single hypothesis `hfam : ConeFamilyAEMeasurableStep`.
* `firstPass_4_2_assembled`: the same conclusion, with `hfam` discharged by `coneFamilyAEMeasurable_proved`.

Open NEW inputs, kept as explicit hypotheses (not proved here):
* `hgap : HarmonicBallStrictObstacleGapStep 𝒮` (Proofs/Sec4/DivSandpileLowerBound/Final.lean:32), the strict obstacle gap.
  Its printed proof, `eq:strictly-above-in-interior` (paper/idla_mated_crt-corrected.tex, label at line 1913, "there exists
  s > 0 by continuity"), does not establish strict positivity on the interior of the closure of the positivity set (audit
  E-x3-1, `StrictGapCounterexample.lean`); the missing ingredient is (2) of audit E-c2-5. With ChatGPT (operator note 23:56).
* `hcan : ConeCanonicalHalfBallStep` (FirstPass/S2g.lean:82) and `hcl : ConeHalfBallClosureInsideStep`
  (Proofs/Sec2/ConeFamilyMeasurable/StoppedClosure.lean:18, documented there as not stated in the paper); they are used
  only by `firstPass_4_2_assembled`.

Both theorems are conditional on `hgap`. The full hypothesis lists are in the docstrings of the two theorems.
-/

namespace MatedCRT

/-- **Proposition 4.2 (first pass), from the cone family step (q4).** Hypotheses, in order:
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

/-- **Proposition 4.2 (first pass), from the two strict-gap steps (q4, fp-S4d-4-2-assembly).** Same conclusion as
`firstPass_4_2_of_coneFamilyStep`, with the open NEW input `hgap` replaced by its two named components
(`FirstPass/S4d/StrictGapReduction.lean`, ChatGPT Section 5): `hdet` (deterministic comparison, Section 2) and `hnj`
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

/-- **Proposition 4.2 (first pass), assembled (q4, fp-S4d-4-2-assembly).** Same conclusion as
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

/-- **Proposition 4.2 (first pass), with the deterministic comparison discharged (q4, fp-S4d-4-2-assembly).** Same
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

/-- **Proposition 4.2 (first pass), final assembly (q4, fp-S4d-4-2-assembly).** The conclusion `DivSandpileLowerBoundStmt 𝒮`
(Draft Proposition 4.2, `Draft/Section4.lean:50`) with every route-level input made explicit. The name `firstPass_4_2`
is taken by FirstPass/S5c.lean (q3's conditional version, with `hgap`), so this is `firstPass_4_2_final`.
Hypotheses, in order:
* cited inputs, as in `firstPass_4_2_of_coneFamilyStep`: `hm`, `h210`, `h34`, `h214`, `h28`, `h35`, `h218`, `h27`, `hH`,
  `hcone`, `h23`, `h24`, `h33`;
* deterministic comparison, discharged by `strictGapDeterministicComparison_of_frozen` from the explicit inputs
  `hG` (`HarmonicBalls.GreenFunctionBallStmt`, Draft), `hpc` (`FrozenPunctureConnected`, Frozen/S4d.lean),
  `hsmp` (`FPStrongMinimumPrinciple`, Frozen/S5c.lean), `hwmp` (`FrozenSuperharmonicMinimumPrinciple`, Frozen/S2g.lean),
  `hpole` (`FrozenGreenDiscPole`, Frozen/S2g.lean);
* open NEW input `hnj : StrictGapFixedTimeUnionStep 𝒮` (fixed-time union, ChatGPT Sections 4-5; the measurability
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


/-- **Proposition 4.2 with the fixed-time union discharged (q4, fp-S4d-4-2-assembly).** The hypothesis `hnj` of
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

end MatedCRT
