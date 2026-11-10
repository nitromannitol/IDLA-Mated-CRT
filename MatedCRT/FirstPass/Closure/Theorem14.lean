import MatedCRT.FirstPass.S1d
import MatedCRT.FirstPass.S3g
import MatedCRT.FirstPass.S3S4b
import MatedCRT.FirstPass.S4d
import MatedCRT.FirstPass.S2g.Draft24
import MatedCRT.FirstPass.S2g.Section6Canonical
import MatedCRT.FirstPass.S3f.FiniteDomainRepresentation
import MatedCRT.FirstPass.Closure.Section2
import MatedCRT.FirstPass.Closure.Section3
import MatedCRT.FirstPass.Closure.Section6
import MatedCRT.FirstPass.Closure.Prop51Cited

/-!
# Theorems 1.4 and 1.6 with the counted providers wired in (fp-main-1-4-1-6-wiring, z5)

`closed_1_4_wired` and `closed_1_6_wired` have the conclusions of `firstPass_1_4` and `firstPass_1_6`
(`MatedCRT/FirstPass/S1d.lean`). They take no raw numbered-result parameter for the four numbered inputs that
`firstPass_1_4` / `firstPass_1_6` take directly: Lemma 3.5 (`h35`), Proposition 4.2 (`h42`), Proposition 5.1 (`h51`) and
Proposition 6.1 (`h61`). Those four are built inside the proof from providers and their own hypotheses:

* `h35` (Lemma 3.5, `DiscreteDirichletProblemStmt`): `FirstPass35Bridge.discreteDirichletProblem_of_corrected`
  (`S3g.lean:49`) with the corrected Lemma 3.5 `firstPass_3_5_corrected` (`S3S4b.lean:43`), its corrected Lemma 3.6
  input `closed_3_6_corrected` (uses `hC`), the proved finite-domain representation
  `frozenFiniteDomainDirichletRepresentation_proved`, and the maximum principle `closed_2_13` (uses `hcell`).
* `h42` (Proposition 4.2, `DivSandpileLowerBoundStmt`): `firstPass_4_2_final` (`S4d.lean:148`). Its input
  `hcone : FrozenConeEnvironmentScaling 𝒮` is supplied by the repaired `hEnvS hsc hrp hind` (the retired frozen name
  is not a binder). Its Lemma 2.5 input `h24` is `coneHarmonicBallsUpToFixedTimeStmt_of_canonical hcan hcl`
  (`S2g/Draft24.lean:65`), and its Lemma 3.3 input `h33` is `firstPass_3_3`.
* `h51` (Proposition 5.1, `IDLALowerBoundStmt`): `closed_5_1_cited` (`Closure/Prop51Cited.lean`) with `hC`.
* `h61` (Proposition 6.1, `IDLAUpperBoundStmt`): `firstPass_6_1_canonical24` (`S2g/Section6Canonical.lean:145`) with
  `h610 : IterativeBoundStmt 𝒮` from `closed_6_10` (uses `hC`). The name `firstPass_6_1` does not occur in the
  repository; the open input of this provider is the corrected canonical Lemma 2.4 `hcan6`, kept as a binder.

The remaining binders are the hypotheses of `firstPass_1_4` / `firstPass_1_6` other than `h35`, `h42`, `h51`, `h61`,
together with the hypotheses of the providers, deduplicated by Lean type. `h218 : ExitTimeUpperBoundStmt 𝒮` is kept as a
binder exactly as in `firstPass_1_4`.
-/

open MeasureTheory
open _root_.HarmonicBalls

namespace MatedCRT.FirstPassClosure

/-- **Theorem 1.4 (wired closure).** The conclusion of `firstPass_1_4`, with `h35`, `h42`, `h51` and `h61` discharged by
the providers listed in the module docstring. -/
theorem closed_1_4_wired {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hscale : QuantumConeScalingInput) (hsc : SLEScaleInvarianceInput 𝒮) (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮) (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮) (hdeg : DegreeBoundInput 𝒮)
    (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction) (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮) (hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected) (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable) (hF3 : FrozenDiskGreenNonnegCont)
    -- inputs of the Lemma 3.5 chain (`h35`)
    (hcell : FrozenAdjacentCellsMeetAe 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    -- inputs of the Proposition 5.1 chain (`h51`, `closed_5_1_cited`)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮) (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw) (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4)
    (hstd : FrozenConeLogLocalCodeLawStd) (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre) (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales) (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero) (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet) (hSC : FrozenClusterStrongCompatibility)
    -- inputs of the Proposition 4.2 chain (`h42`)
    (hGBall : _root_.HarmonicBalls.GreenFunctionBallStmt) (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple) (hpole : FrozenGreenDiscPole)
    (hnj : StrictGapFixedTimeUnionStep 𝒮) (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep)
    -- input of the Proposition 6.1 chain (`h61`), the corrected canonical Lemma 2.4
    (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt) :
    ConvergenceOfIDLAStmt 𝒮 := by
  have h34 : IntegralConvergenceGreenFunctionStmt 𝒮 := S3S4c.firstPass_3_4 h27 h218 hm hrevuz hdet
  have h33 : UniformConvergenceGreenKernelStmt 𝒮 := firstPass_3_3 h210 h34 h214 h28 h27 h218 hm hH
  have hmax : MaximumPrincipleStmt 𝒮 := closed_2_13 hcell
  have h36 : CorrectedHarmonicConvergenceStmt 𝒮 := closed_3_6_corrected ν hC hexc
  have h35c : DiscreteDirichletProblemCorrectedStmt 𝒮 :=
    firstPass_3_5_corrected h27 hm h210 h34 h214 h28 h218 hH MatedCRT.FirstPass37.frozenFiniteDomainDirichletRepresentation_proved h36
  have h35 : DiscreteDirichletProblemStmt 𝒮 :=
    FirstPass35Bridge.discreteDirichletProblem_of_corrected h28 hmax h35c
  have h24 : ConeHarmonicBallsUpToFixedTimeStmt := coneHarmonicBallsUpToFixedTimeStmt_of_canonical hcan hcl
  have h42 : DivSandpileLowerBoundStmt 𝒮 :=
    firstPass_4_2_final hm h210 h34 h214 h28 h35 h218 h27 hH (hEnvS hsc hrp hind) h23 h24 h33 hGBall hpc hsmp hmin
      hpole hnj hcan hcl hE1 hE2 hscale h22
  have h51 : IDLALowerBoundStmt 𝒮 :=
    closed_5_1_cited ν hC hμae hSB hsup hcell hF1 hexc hpole hmodel hFL hLoc hpair hF2 hstd hmin hGBC hconf hK hE
      hE1 hE2 hscale h27 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC
  have h610 : IterativeBoundStmt 𝒮 := closed_6_10 ν hC h27 h0 h2 hV hR
  have h61 : IDLAUpperBoundStmt 𝒮 := firstPass_6_1_canonical24 𝒮 h610 h51 hcan6
  exact firstPass_1_4 𝒮 hscale hsc hrp hind hEnvS hm hdeg h27 h28 h29 h210 h214 h216 h218 hH h0 h2 hV hR hcone
    hrevuz hdet h35 h42 h51 h61 h23 hdiv hF1 hF2 hF3

/-- **Theorem 1.6 (wired closure).** The conclusion of `firstPass_1_6`, with the same binders and the same discharged
inputs as `closed_1_4_wired`. -/
theorem closed_1_6_wired {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hscale : QuantumConeScalingInput) (hsc : SLEScaleInvarianceInput 𝒮) (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮) (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮) (hdeg : DegreeBoundInput 𝒮)
    (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction) (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮) (hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected) (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable) (hF3 : FrozenDiskGreenNonnegCont)
    -- inputs of the Lemma 3.5 chain (`h35`)
    (hcell : FrozenAdjacentCellsMeetAe 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    -- inputs of the Proposition 5.1 chain (`h51`, `closed_5_1_cited`)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮) (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw) (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4)
    (hstd : FrozenConeLogLocalCodeLawStd) (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre) (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales) (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero) (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet) (hSC : FrozenClusterStrongCompatibility)
    -- inputs of the Proposition 4.2 chain (`h42`)
    (hGBall : _root_.HarmonicBalls.GreenFunctionBallStmt) (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple) (hpole : FrozenGreenDiscPole)
    (hnj : StrictGapFixedTimeUnionStep 𝒮) (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep)
    -- input of the Proposition 6.1 chain (`h61`), the corrected canonical Lemma 2.4
    (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt) :
    ConvergenceOfDivSandpileStmt 𝒮 := by
  have h34 : IntegralConvergenceGreenFunctionStmt 𝒮 := S3S4c.firstPass_3_4 h27 h218 hm hrevuz hdet
  have h33 : UniformConvergenceGreenKernelStmt 𝒮 := firstPass_3_3 h210 h34 h214 h28 h27 h218 hm hH
  have hmax : MaximumPrincipleStmt 𝒮 := closed_2_13 hcell
  have h36 : CorrectedHarmonicConvergenceStmt 𝒮 := closed_3_6_corrected ν hC hexc
  have h35c : DiscreteDirichletProblemCorrectedStmt 𝒮 :=
    firstPass_3_5_corrected h27 hm h210 h34 h214 h28 h218 hH MatedCRT.FirstPass37.frozenFiniteDomainDirichletRepresentation_proved h36
  have h35 : DiscreteDirichletProblemStmt 𝒮 :=
    FirstPass35Bridge.discreteDirichletProblem_of_corrected h28 hmax h35c
  have h24 : ConeHarmonicBallsUpToFixedTimeStmt := coneHarmonicBallsUpToFixedTimeStmt_of_canonical hcan hcl
  have h42 : DivSandpileLowerBoundStmt 𝒮 :=
    firstPass_4_2_final hm h210 h34 h214 h28 h35 h218 h27 hH (hEnvS hsc hrp hind) h23 h24 h33 hGBall hpc hsmp hmin
      hpole hnj hcan hcl hE1 hE2 hscale h22
  have h51 : IDLALowerBoundStmt 𝒮 :=
    closed_5_1_cited ν hC hμae hSB hsup hcell hF1 hexc hpole hmodel hFL hLoc hpair hF2 hstd hmin hGBC hconf hK hE
      hE1 hE2 hscale h27 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC
  have h610 : IterativeBoundStmt 𝒮 := closed_6_10 ν hC h27 h0 h2 hV hR
  have h61 : IDLAUpperBoundStmt 𝒮 := firstPass_6_1_canonical24 𝒮 h610 h51 hcan6
  exact firstPass_1_6 𝒮 hscale hsc hrp hind hEnvS hm hdeg h27 h28 h29 h210 h214 h216 h218 hH h0 h2 hV hR hcone
    hrevuz hdet h35 h42 h51 h61 h23 hdiv hF1 hF2 hF3

end MatedCRT.FirstPassClosure

#print axioms MatedCRT.FirstPassClosure.closed_1_4_wired
#print axioms MatedCRT.FirstPassClosure.closed_1_6_wired
