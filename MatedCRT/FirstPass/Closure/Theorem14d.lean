import MatedCRT.FirstPass.Closure.Theorem14
import MatedCRT.FirstPass.S218
import MatedCRT.Proofs.Sec3.ConeBallMass
import MatedCRT.FirstPass.Frozen.S5Cited
import MatedCRT.FirstPass.S3t.BLEnvelopeClosure

/-!
# Theorems 1.4 and 1.6 with the exit-time bound, the volume growth and the truncated laws derived

`closed_1_4_derived` and `closed_1_6_derived` have the conclusions of `closed_1_4_wired` and `closed_1_6_wired`
(`Closure/Theorem14.lean`, not edited here). Three of their inputs are replaced.

* (i) `h218 : ExitTimeUpperBoundStmt 𝒮` is derived: `exitTimeUpperBound_of_bg20Prop51_volumeGrowth h51 h27`
  (`MatedCRT/FirstPass/S218.lean`), from the new binder `h51 : BG20Prop51 𝒮` (BG20 Proposition 5.1, frozen).
* (ii) `h27 : VolumeGrowthStmt` (IDLA Lemma 2.7) is derived: `volumeGrowthStmt_of_berestyckiGwynne hBG`
  (`MatedCRT/Proofs/Sec3/ConeBallMass.lean:17`), from the new binder `hBG : FrozenBerestyckiGwynneConeBallMass`
  (`FirstPass/Frozen/S5Cited.lean:35`, definitionally `BerestyckiGwynneConeBallMassStmt`). The name
  `volumeGrowth_of_coneBallMass` does not occur in the repository; `FirstPass/S5u.lean` only
  documents this provider.
* (iii) `hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮` is derived: `MatedCRT.TruncatedLaws.truncatedQuenchedLawsFixedTime_of_inputs`
  (`FirstPass/S3t/BLEnvelopeClosure.lean`, committed 4c8c580) applied to
  `h211 := MatedCRT.CertifiedReferenceModel.randomWalkToLBM hC` (Theorem 2.11 from the certified model), `h28`, `hm`
  and `hexc`. The former binder `hT` (same convention as `FirstPass/S5qd.lean`) is removed.

`hrevuz : FrozenLBMGreenOccupationRescaled 𝒮` (the Revuz occupation identity, source gap) is kept as in
`closed_1_4_wired`. The other binders are the binders of `closed_1_4_wired` / `closed_1_6_wired`, deduplicated.
Terminology: Berestycki–Gwynne (BG20) for the cone ball mass and the exit time; Berestycki–Powell for the Green
function; Armitage–Gardiner for the killed Green function.
-/

open MeasureTheory
open _root_.HarmonicBalls

namespace MatedCRT.FirstPassClosure

/-- **Theorem 1.4 (wired closure, derived inputs).** The conclusion of `closed_1_4_wired`, with `h218` derived from
`h51` and `h27`, `h27` derived from `hBG`, and `hdet` derived from `truncatedQuenchedLawsFixedTime_of_inputs` (see the module
docstring). -/
theorem closed_1_4_derived {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hscale : QuantumConeScalingInput) (hsc : SLEScaleInvarianceInput 𝒮) (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮) (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮) (hdeg : DegreeBoundInput 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h51 : BG20Prop51 𝒮) (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction) (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
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
  have h27 : VolumeGrowthStmt := volumeGrowthStmt_of_berestyckiGwynne hBG
  have h218 : ExitTimeUpperBoundStmt 𝒮 := exitTimeUpperBound_of_bg20Prop51_volumeGrowth h51 h27
  have hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮 :=
    MatedCRT.TruncatedLaws.truncatedQuenchedLawsFixedTime_of_inputs
      (MatedCRT.CertifiedReferenceModel.randomWalkToLBM hC) h28 hm hexc
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
  have hIDLA : IDLALowerBoundStmt 𝒮 :=
    closed_5_1_cited ν hC hμae hSB hsup hcell hF1 hexc hpole hmodel hFL hLoc hpair hF2 hstd hmin hGBC hconf hK hE
      hE1 hE2 hscale h27 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC
  have h610 : IterativeBoundStmt 𝒮 := closed_6_10 ν hC h27 h0 h2 hV hR
  have h61 : IDLAUpperBoundStmt 𝒮 := firstPass_6_1_canonical24 𝒮 h610 hIDLA hcan6
  exact firstPass_1_4 𝒮 hscale hsc hrp hind hEnvS hm hdeg h27 h28 h29 h210 h214 h216 h218 hH h0 h2 hV hR hcone
    hrevuz hdet h35 h42 hIDLA h61 h23 hdiv hF1 hF2 hF3

/-- **Theorem 1.6 (wired closure, derived inputs).** The conclusion of `closed_1_6_wired`, with the same derived inputs
as `closed_1_4_derived`. -/
theorem closed_1_6_derived {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hscale : QuantumConeScalingInput) (hsc : SLEScaleInvarianceInput 𝒮) (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮) (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮) (hdeg : DegreeBoundInput 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h51 : BG20Prop51 𝒮) (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction) (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
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
  have h27 : VolumeGrowthStmt := volumeGrowthStmt_of_berestyckiGwynne hBG
  have h218 : ExitTimeUpperBoundStmt 𝒮 := exitTimeUpperBound_of_bg20Prop51_volumeGrowth h51 h27
  have hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮 :=
    MatedCRT.TruncatedLaws.truncatedQuenchedLawsFixedTime_of_inputs
      (MatedCRT.CertifiedReferenceModel.randomWalkToLBM hC) h28 hm hexc
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
  have hIDLA : IDLALowerBoundStmt 𝒮 :=
    closed_5_1_cited ν hC hμae hSB hsup hcell hF1 hexc hpole hmodel hFL hLoc hpair hF2 hstd hmin hGBC hconf hK hE
      hE1 hE2 hscale h27 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC
  have h610 : IterativeBoundStmt 𝒮 := closed_6_10 ν hC h27 h0 h2 hV hR
  have h61 : IDLAUpperBoundStmt 𝒮 := firstPass_6_1_canonical24 𝒮 h610 hIDLA hcan6
  exact firstPass_1_6 𝒮 hscale hsc hrp hind hEnvS hm hdeg h27 h28 h29 h210 h214 h216 h218 hH h0 h2 hV hR hcone
    hrevuz hdet h35 h42 hIDLA h61 h23 hdiv hF1 hF2 hF3

end MatedCRT.FirstPassClosure

#print axioms MatedCRT.FirstPassClosure.closed_1_4_derived
#print axioms MatedCRT.FirstPassClosure.closed_1_6_derived
