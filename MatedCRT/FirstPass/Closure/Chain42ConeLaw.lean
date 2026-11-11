import MatedCRT.FirstPass.Closure.H35CorrectedRewire
import MatedCRT.FirstPass.Closure.Steps42
import MatedCRT.FirstPass.Closure.HSCDerived
import MatedCRT.FirstPass.Closure.OwnBinderRewire
import MatedCRT.FirstPass.S5r.ClosureInside
import MatedCRT.Proofs.Sec3.ConeBallMass

/-! # Proposition 4.2 along the repaired cone-scaling input

The copies of `H35CorrectedRewire.lean` bind the false `FrozenConeEnvironmentScaling` (Frozen/S3S4.lean:27) through the
chain `firstPass_4_2_of_coneFamilyStep` → `firstPass_4_1`. The copies below replace the cone-scaling input by
`FrozenConeScalingLaw` (Frozen/S4S6c.lean:18) and the Lemma 4.1 call by `firstPass_4_1_coneLaw_h35c`
(H35CorrectedRewire.lean). The Lemma 3.5 binder is the corrected form `DiscreteDirichletProblemCorrectedStmt`,
and the Lemma 2.4 binder is the corrected form `ConeHarmonicBallsUpToFixedTimeCorrectedStmt`. The bodies are those
of the copies they replace; the originals are unchanged.
-/

namespace MatedCRT

open MeasureTheory Set
open _root_.HarmonicBalls

section ChainConeLaw

/-- Proposition 4.2 from the cone family step, with the repaired cone-scaling input `FrozenConeScalingLaw`. Copy of
`firstPass_4_2_of_coneFamilyStep_h24c` (H35CorrectedRewire.lean). Binder diff against that copy: `h35`
(Draft `DiscreteDirichletProblemStmt`) becomes `h35c` (`DiscreteDirichletProblemCorrectedStmt`), and `hcone`
(`FrozenConeEnvironmentScaling`, false) becomes `FrozenConeScalingLaw`. The conclusion is the same. -/
theorem firstPass_4_2_of_coneFamilyStep_coneLaw {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h35c : DiscreteDirichletProblemCorrectedStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeScalingLaw 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (hgap : HarmonicBallStrictObstacleGapStep 𝒮)
    (hfam : ConeFamilyAEMeasurableStep) :
    DivSandpileLowerBoundStmt 𝒮 :=
  divSandpileLowerBound_final_h24c 𝒮
    (firstPass_4_1_coneLaw_h35c hm h210 h34 h214 h28 h35c h218 h27 hH hcone) h23 h24c h27 h28 h33 hfam hgap

/-- Proposition 4.2 from the two strict-gap steps, with `FrozenConeScalingLaw`. Copy of
`firstPass_4_2_of_strictGapSteps_h24c` (H35CorrectedRewire.lean), with the same binder diff as
`firstPass_4_2_of_coneFamilyStep_coneLaw`. -/
theorem firstPass_4_2_of_strictGapSteps_coneLaw {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h35c : DiscreteDirichletProblemCorrectedStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeScalingLaw 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (hdet : StrictGapDeterministicComparisonStep) (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hfam : ConeFamilyAEMeasurableStep) :
    DivSandpileLowerBoundStmt 𝒮 :=
  firstPass_4_2_of_coneFamilyStep_coneLaw hm h210 h34 h214 h28 h35c h218 h27 hH hcone h23 h24c h33
    (harmonicBallStrictObstacleGapStep_of_steps 𝒮 hdet hnj) hfam

/-- Proposition 4.2 from the frozen strict-gap inputs, with `FrozenConeScalingLaw`. Copy of
`firstPass_4_2_of_frozen_strictGap_h24c` (H35CorrectedRewire.lean), with the same binder diff. -/
theorem firstPass_4_2_of_frozen_strictGap_coneLaw {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h35c : DiscreteDirichletProblemCorrectedStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeScalingLaw 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (hG : _root_.HarmonicBalls.GreenFunctionBallStmt) (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple) (hwmp : FrozenSuperharmonicMinimumPrinciple)
    (hpole : FrozenGreenDiscPole)
    (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hfam : ConeFamilyAEMeasurableStep) :
    DivSandpileLowerBoundStmt 𝒮 :=
  firstPass_4_2_of_strictGapSteps_coneLaw hm h210 h34 h214 h28 h35c h218 h27 hH hcone h23 h24c h33
    (strictGapDeterministicComparison_of_frozen hG hpc hsmp hwmp hpole) hnj hfam

/-- Proposition 4.2 (`DivSandpileLowerBoundStmt`) in final form with `FrozenConeScalingLaw`. Copy of
`firstPass_4_2_final_h35c` (H35CorrectedRewire.lean), with the same binder diff: `h35` → `h35c`, and `hcone` →
`FrozenConeScalingLaw`. All other binders and the conclusion are those of `firstPass_4_2_final_h35c`. -/
theorem firstPass_4_2_final_coneLaw {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h35c : DiscreteDirichletProblemCorrectedStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeScalingLaw 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (hG : _root_.HarmonicBalls.GreenFunctionBallStmt) (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple) (hwmp : FrozenSuperharmonicMinimumPrinciple)
    (hpole : FrozenGreenDiscPole)
    (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hcan : ConeCanonicalHalfBallStep) (hcl : ConeHalfBallClosureInsideStep)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt) :
    DivSandpileLowerBoundStmt 𝒮 :=
  firstPass_4_2_of_frozen_strictGap_coneLaw hm h210 h34 h214 h28 h35c h218 h27 hH hcone h23 h24c h33 hG hpc hsmp
    hwmp hpole hnj (coneFamilyAEMeasurable_proved hcan hcl h27 hE1 hE2 hscale h22)

/-- **Proposition 4.2, counted form without the false cone-scaling hypothesis.** `firstPass_4_2_final_coneLaw` with
the paper-own steps of Proposition 4.2 discharged:
* `hcan = ConeCanonicalHalfBallStep` (FirstPass/S2g.lean:81) by `coneCanonicalHalfBallStep_proof`
  (FirstPass/Closure/Steps42.lean:36), the projection of the canonical Lemma 2.4;
* `hcl = ConeHalfBallClosureInsideStep` (Proofs/Sec2/ConeFamilyMeasurable/StoppedClosure.lean:18) by
  `MatedCRT.S5r.coneHalfBallClosureInsideStep_corrected` (FirstPass/S5r/ClosureInside.lean);
* `hnj = StrictGapFixedTimeUnionStep 𝒮` (FirstPass/S4d/StrictGapReduction.lean:35) by
  `strictGapFixedTimeUnionStep_proof` (FirstPass/Closure/Steps42.lean:60), which takes `hcl`;
* `hSC = ClusterStrongCompatibilityStmt.{0}` by `frozenClusterStrongCompatibility_of_volumeGrowth hI2`
  (FirstPass/Closure/HSCDerived.lean);
* `h27 = VolumeGrowthStmt` by `volumeGrowthStmt_of_berestyckiGwynne hBG` (Proofs/Sec3/ConeBallMass.lean:17), and
  `h22 = LQGMeasurePropertiesStmt` by `closed_2_2_ownBinders hscale hBG hND` (FirstPass/Closure/OwnBinderRewire.lean:116),
  as in the proof of `strictGapFixedTimeUnionStep_proof`.
The binders are the Frozen and cited inputs of those steps, the Lemma 3.5 and Lemma 2.4 corrected forms, the cited
Lemmas 2.8 (`h28`), 2.10, 2.14, 2.18 and 3.3 (the Draft forms of this first pass), and `hcone : FrozenConeScalingLaw 𝒮`. -/
theorem closed_4_2_clean {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h35c : DiscreteDirichletProblemCorrectedStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeScalingLaw 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (hG : _root_.HarmonicBalls.GreenFunctionBallStmt) (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple) (hwmp : FrozenSuperharmonicMinimumPrinciple)
    (hpole : FrozenGreenDiscPole)
    (hstd : FrozenConeLogLocalCodeLawStd) (hCentre : FrozenGreenBallCentre)
    (hOpen : ClusterOpenLaplacianStmt.{0}) (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0}) (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0}) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0}) (hconf : FrozenHBInitialConfinement)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw) (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (hND : LQGMeasureNonDyadicDilationPart)
    (hrescale : ConeRescaledMeasureIsConeFieldInput) :
    DivSandpileLowerBoundStmt 𝒮 := by
  have hSC : ClusterStrongCompatibilityStmt.{0} := frozenClusterStrongCompatibility_of_volumeGrowth hI2
  have h27 : VolumeGrowthStmt := volumeGrowthStmt_of_berestyckiGwynne hBG
  have hcan : ConeCanonicalHalfBallStep :=
    MatedCRT.FirstPassClosure.coneCanonicalHalfBallStep_proof hstd hCentre hOpen hSup hCons hMono hCompat hBdry hExist
      hThm11 hProp56 hconf hI2 hK hloc hSC hE hFL hBG
  have hcl : ConeHalfBallClosureInsideStep :=
    MatedCRT.S5r.coneHalfBallClosureInsideStep_corrected hI2 hK hloc hExist hSC h27 hE hFL
  have hnj : StrictGapFixedTimeUnionStep 𝒮 :=
    MatedCRT.FirstPassClosure.strictGapFixedTimeUnionStep_proof hstd hCentre hOpen hSup hCons hMono hCompat hBdry hExist
      hThm11 hProp56 hconf hI2 hK hloc hSC hE hFL hBG hE1 hE2 hscale hND hrescale hcl
  have h22 : LQGMeasurePropertiesStmt := closed_2_2_ownBinders hscale hBG hND
  exact firstPass_4_2_final_coneLaw hm h210 h34 h214 h28 h35c h218 h27 hH hcone h23 h24c h33 hG hpc hsmp hwmp hpole
    hnj hcan hcl hE1 hE2 hscale h22

end ChainConeLaw

#print axioms firstPass_4_2_of_coneFamilyStep_coneLaw
#print axioms firstPass_4_2_final_coneLaw
#print axioms closed_4_2_clean

end MatedCRT
