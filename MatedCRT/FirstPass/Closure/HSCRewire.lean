import MatedCRT.FirstPass.Closure.HSCDerived
import MatedCRT.FirstPass.Closure.Final14Full
import MatedCRT.FirstPass.Closure.CellRewire
import MatedCRT.FirstPass.Closure.H24cBridge
import MatedCRT.FirstPass.Main
import MatedCRT.FirstPass.Closure.OwnBinderRewire
import MatedCRT.FirstPass.S2g.Assembly2456

/-!
# Counted forms with the cluster strong compatibility binder discharged from volume growth

For each counted form of the ledger `docs/campaign/COUNTED.md` that binds `FrozenClusterStrongCompatibility` or
`ClusterStrongCompatibilityStmt.{0}`, the wrapper `<name>_noSC` binds the volume growth input instead
(`FrozenLQGVolumeGrowthAllScales` or `LQGVolumeGrowthAllScalesStmt.{0}`, the input `hI2` of the Harmonic-Balls paper)
and discharges the cluster strong compatibility binder by `MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth`
(`MatedCRT/FirstPass/Closure/HSCDerived.lean`), that is Lemma 5.8 (cluster strong compatibility) of the
Harmonic-Balls paper, derived from the all-scales volume growth estimate. The conclusion and every other binder of
each counted form are unchanged.
-/

section
namespace MatedCRT
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- `closed_1_4_full` with the cluster strong compatibility binder (hSC, hSCHB) discharged from the
  volume growth input (Lemma 5.8, `MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth`,
  MatedCRT/FirstPass/Closure/HSCDerived.lean). The conclusion and every other binder are unchanged.
  -/
theorem closed_1_4_full_noSC
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero)
    (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hBdryHB : ClusterBoundaryMeasureZeroStmt.{0})
    (hExistHB : ExistenceHarmonicBallsStmt.{0})
    (hProp56HB : UniquenessHarmonicBallsStmt.{0})
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0})
    (hlocHB : HarmonicBallLocalSetStmt.{0})
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGB : HarmonicBalls.GreenFunctionBallStmt)
    (hpole : FrozenGreenDiscPole)
    : ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_full (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hscale := hscale) (hsc := hsc) (hrp := hrp)
    (hind := hind) (hEnvS := hEnvS) (hBG := hBG) (h0 := h0) (h2 := h2) (hV := hV) (hdiv := hdiv)
    (hF3 := hF3) (hsup := hsup) (hmodel := hmodel) (hFL := hFL) (hstd := hstd) (hGBC := hGBC) (hconf
    := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (hG15 := hG15) (h32 := h32) (h611 :=
    h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat :=
    hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc)
    (hSC := _root_.MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth hI2) (hrescale :=
    hrescale) (hND := hND) (hBdryHB := hBdryHB) (hExistHB := hExistHB) (hProp56HB := hProp56HB)
    (hI2HB := hI2HB) (hlocHB := hlocHB) (hSCHB :=
    _root_.MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth hI2) (hU := hU) (hmeasT :=
    hmeasT) (hmin := hmin) (hGB := hGB) (hpole := hpole)

/-- `closed_1_6_full` with the cluster strong compatibility binder (hSC, hSCHB) discharged from the
  volume growth input (Lemma 5.8, `MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth`,
  MatedCRT/FirstPass/Closure/HSCDerived.lean). The conclusion and every other binder are unchanged.
  -/
theorem closed_1_6_full_noSC
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero)
    (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hBdryHB : ClusterBoundaryMeasureZeroStmt.{0})
    (hExistHB : ExistenceHarmonicBallsStmt.{0})
    (hProp56HB : UniquenessHarmonicBallsStmt.{0})
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0})
    (hlocHB : HarmonicBallLocalSetStmt.{0})
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGB : HarmonicBalls.GreenFunctionBallStmt)
    (hpole : FrozenGreenDiscPole)
    : ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_full (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hscale := hscale) (hsc := hsc) (hrp := hrp)
    (hind := hind) (hEnvS := hEnvS) (hBG := hBG) (h0 := h0) (h2 := h2) (hV := hV) (hdiv := hdiv)
    (hF3 := hF3) (hsup := hsup) (hmodel := hmodel) (hFL := hFL) (hstd := hstd) (hGBC := hGBC) (hconf
    := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (hG15 := hG15) (h32 := h32) (h611 :=
    h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat :=
    hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc)
    (hSC := _root_.MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth hI2) (hrescale :=
    hrescale) (hND := hND) (hBdryHB := hBdryHB) (hExistHB := hExistHB) (hProp56HB := hProp56HB)
    (hI2HB := hI2HB) (hlocHB := hlocHB) (hSCHB :=
    _root_.MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth hI2) (hU := hU) (hmeasT :=
    hmeasT) (hmin := hmin) (hGB := hGB) (hpole := hpole)

/-- `closed_2_3_lit` with the cluster strong compatibility binder (hSCHB) discharged from the volume
  growth input (Lemma 5.8, `MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth`,
  MatedCRT/FirstPass/Closure/HSCDerived.lean). The conclusion and every other binder are unchanged.
  -/
theorem closed_2_3_lit_noSC
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hscale : QuantumConeScalingInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hGBC : FrozenGreenBallCentre)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdryHB : ClusterBoundaryMeasureZeroStmt.{0})
    (hExistHB : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56HB : UniquenessHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hlocHB : HarmonicBallLocalSetStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGB : HarmonicBalls.GreenFunctionBallStmt)
    (hpole : FrozenGreenDiscPole)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    : ConeHarmonicBallsStmt :=
  closed_2_3_lit (hBG := hBG) (hscale := hscale) (hND := hND) (hstd := hstd) (hGBC := hGBC) (h32 :=
    h32) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdryHB := hBdryHB)
    (hExistHB := hExistHB) (hThm11 := hThm11) (hProp56HB := hProp56HB) (hconf := hconf) (hI2HB :=
    hI2HB) (hK := hK) (hlocHB := hlocHB) (hSCHB :=
    _root_.MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth hI2HB) (hE := hE) (hFL := hFL)
    (hE1 := hE1) (hE2 := hE2) (hU := hU) (hmeasT := hmeasT) (hmin := hmin) (hGB := hGB) (hpole :=
    hpole) (hrescale := hrescale)

end MatedCRT
end

section
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls
namespace MatedCRT.FirstPassClosure

/-- `closed_5_1_cellRewire` with the cluster strong compatibility binder (hSC) discharged from the
  volume growth input (Lemma 5.8, `MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth`,
  MatedCRT/FirstPass/Closure/HSCDerived.lean). The conclusion and every other binder are unchanged.
  -/
theorem closed_5_1_cellRewire_noSC
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮)
    (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮)
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hG : FrozenGreenDiscPole)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality)
    (hpair : FPPairingLawIG4)
    (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput)
    (h27 : VolumeGrowthStmt)
    (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (hG15 : GreenFunctionCrudeBoundStmt 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{0})
    (h82 : TypicalPointManyGoodScalesStmt.{0})
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hEx : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hloc : HarmonicBallLocalSetStmt.{0})
    : IDLALowerBoundStmt 𝒮 :=
  closed_5_1_cellRewire (𝒮 := 𝒮) (ν := ν) (hC := hC) (hμae := hμae) (hSB := hSB) (hsup := hsup) (hU
    := hU) (hexc := hexc) (hG := hG) (hmodel := hmodel) (hFL := hFL) (hLoc := hLoc) (hpair := hpair)
    (hmeasT := hmeasT) (hstd := hstd) (hmin := hmin) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE
    := hE) (hE1 := hE1) (hE2 := hE2) (hscale := hscale) (h27 := h27) (h22 := h22) (h24c := h24c)
    (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons :=
    hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11)
    (hProp56 := hProp56) (hloc := hloc) (hSC :=
    _root_.MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth hI2)

end MatedCRT.FirstPassClosure
end

section
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls MatedCRT.FirstPassClosure
namespace MatedCRT.FirstPassClosure

/-- `closed_5_1_ownBinders` with the cluster strong compatibility binder (hSC) discharged from the
  volume growth input (Lemma 5.8, `MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth`,
  MatedCRT/FirstPass/Closure/HSCDerived.lean). The conclusion and every other binder are unchanged.
  -/
theorem closed_5_1_ownBinders_noSC
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮)
    (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮)
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hG : FrozenGreenDiscPole)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality)
    (hpair : FPPairingLawIG4)
    (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput)
    (h22 : LQGMeasurePropertiesStmt)
    (hG15 : GreenFunctionCrudeBoundStmt 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{0})
    (h82 : TypicalPointManyGoodScalesStmt.{0})
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hEx : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    : IDLALowerBoundStmt 𝒮 :=
  closed_5_1_ownBinders (𝒮 := 𝒮) (ν := ν) (hC := hC) (hμae := hμae) (hSB := hSB) (hsup := hsup) (hU
    := hU) (hexc := hexc) (hG := hG) (hmodel := hmodel) (hFL := hFL) (hLoc := hLoc) (hpair := hpair)
    (hmeasT := hmeasT) (hstd := hstd) (hmin := hmin) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE
    := hE) (hE1 := hE1) (hE2 := hE2) (hscale := hscale) (h22 := h22) (hG15 := hG15) (h32 := h32)
    (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono)
    (hCompat := hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc
    := hloc) (hSC := _root_.MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth hI2) (hBG :=
    hBG)

end MatedCRT.FirstPassClosure
end

section
namespace MatedCRT
section Counted
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- `firstPassMain_1_4_full` with the cluster strong compatibility binder (hSC, hSCHB) discharged
  from the volume growth input (Lemma 5.8,
  `MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth`,
  MatedCRT/FirstPass/Closure/HSCDerived.lean). The conclusion and every other binder are unchanged.
  -/
theorem firstPassMain_1_4_full_noSC
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero)
    (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hBdryHB : ClusterBoundaryMeasureZeroStmt.{0})
    (hExistHB : ExistenceHarmonicBallsStmt.{0})
    (hProp56HB : UniquenessHarmonicBallsStmt.{0})
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0})
    (hlocHB : HarmonicBallLocalSetStmt.{0})
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGB : HarmonicBalls.GreenFunctionBallStmt)
    (hpole : FrozenGreenDiscPole)
    : ConvergenceOfIDLAStmt 𝒮 :=
  firstPassMain_1_4_full (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hscale := hscale) (hsc := hsc) (hrp :=
    hrp) (hind := hind) (hEnvS := hEnvS) (hBG := hBG) (h0 := h0) (h2 := h2) (hV := hV) (hdiv :=
    hdiv) (hF3 := hF3) (hsup := hsup) (hmodel := hmodel) (hFL := hFL) (hstd := hstd) (hGBC := hGBC)
    (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (hG15 := hG15) (h32 := h32)
    (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono)
    (hCompat := hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc
    := hloc) (hSC := _root_.MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth hI2) (hrescale
    := hrescale) (hND := hND) (hBdryHB := hBdryHB) (hExistHB := hExistHB) (hProp56HB := hProp56HB)
    (hI2HB := hI2HB) (hlocHB := hlocHB) (hSCHB :=
    _root_.MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth hI2) (hU := hU) (hmeasT :=
    hmeasT) (hmin := hmin) (hGB := hGB) (hpole := hpole)

/-- `firstPassMain_1_6_full` with the cluster strong compatibility binder (hSC, hSCHB) discharged
  from the volume growth input (Lemma 5.8,
  `MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth`,
  MatedCRT/FirstPass/Closure/HSCDerived.lean). The conclusion and every other binder are unchanged.
  -/
theorem firstPassMain_1_6_full_noSC
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero)
    (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hBdryHB : ClusterBoundaryMeasureZeroStmt.{0})
    (hExistHB : ExistenceHarmonicBallsStmt.{0})
    (hProp56HB : UniquenessHarmonicBallsStmt.{0})
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0})
    (hlocHB : HarmonicBallLocalSetStmt.{0})
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGB : HarmonicBalls.GreenFunctionBallStmt)
    (hpole : FrozenGreenDiscPole)
    : ConvergenceOfDivSandpileStmt 𝒮 :=
  firstPassMain_1_6_full (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hscale := hscale) (hsc := hsc) (hrp :=
    hrp) (hind := hind) (hEnvS := hEnvS) (hBG := hBG) (h0 := h0) (h2 := h2) (hV := hV) (hdiv :=
    hdiv) (hF3 := hF3) (hsup := hsup) (hmodel := hmodel) (hFL := hFL) (hstd := hstd) (hGBC := hGBC)
    (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (hG15 := hG15) (h32 := h32)
    (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono)
    (hCompat := hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc
    := hloc) (hSC := _root_.MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth hI2) (hrescale
    := hrescale) (hND := hND) (hBdryHB := hBdryHB) (hExistHB := hExistHB) (hProp56HB := hProp56HB)
    (hI2HB := hI2HB) (hlocHB := hlocHB) (hSCHB :=
    _root_.MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth hI2) (hU := hU) (hmeasT :=
    hmeasT) (hmin := hmin) (hGB := hGB) (hpole := hpole)

end Counted
end MatedCRT
end

section
namespace MatedCRT
open MeasureTheory
open _root_.HarmonicBalls

/-- `firstPass_2_4_ownBinders` with the cluster strong compatibility binder (hSC) discharged from
  the volume growth input (Lemma 5.8, `MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth`,
  MatedCRT/FirstPass/Closure/HSCDerived.lean). The conclusion and every other binder are unchanged.
  -/
theorem firstPass_2_4_ownBinders_noSC
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hCentre : FrozenGreenBallCentre)
    (hOpen : ClusterOpenLaplacianStmt.{0})
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    : ConeHarmonicBallsUpToFixedTimeCanonicalStmt :=
  firstPass_2_4_ownBinders (hstd := hstd) (hCentre := hCentre) (hOpen := hOpen) (hSup := hSup)
    (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hExist := hExist)
    (hThm11 := hThm11) (hProp56 := hProp56) (hconf := hconf) (hI2 := hI2) (hK := hK) (hloc := hloc)
    (hSC := _root_.MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth hI2) (hE := hE) (hFL :=
    hFL) (hBG := hBG)

/-- `firstPass_2_5_ownBinders` with the cluster strong compatibility binder (hSC) discharged from
  the volume growth input (Lemma 5.8, `MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth`,
  MatedCRT/FirstPass/Closure/HSCDerived.lean). The conclusion and every other binder are unchanged.
  -/
theorem firstPass_2_5_ownBinders_noSC
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hCentre : FrozenGreenBallCentre)
    (hOpen : ClusterOpenLaplacianStmt.{0})
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    : ConeScaleInvarianceUpToFixedTimeCanonicalStmt :=
  firstPass_2_5_ownBinders (hstd := hstd) (hCentre := hCentre) (hOpen := hOpen) (hSup := hSup)
    (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hExist := hExist)
    (hThm11 := hThm11) (hProp56 := hProp56) (hconf := hconf) (hI2 := hI2) (hK := hK) (hloc := hloc)
    (hSC := _root_.MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth hI2) (hE := hE) (hFL :=
    hFL) (hBG := hBG) (hE1 := hE1) (hE2 := hE2) (hscale := hscale) (hND := hND)

/-- `firstPass_2_6_ownBinders` with the cluster strong compatibility binder (hSC) discharged from
  the volume growth input (Lemma 5.8, `MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth`,
  MatedCRT/FirstPass/Closure/HSCDerived.lean). The conclusion and every other binder are unchanged.
  -/
theorem firstPass_2_6_ownBinders_noSC
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hCentre : FrozenGreenBallCentre)
    (hOpen : ClusterOpenLaplacianStmt.{0})
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    : ConeScaleInvarianceStmt :=
  firstPass_2_6_ownBinders (hstd := hstd) (hCentre := hCentre) (hOpen := hOpen) (hSup := hSup)
    (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hExist := hExist)
    (hThm11 := hThm11) (hProp56 := hProp56) (hconf := hconf) (hI2 := hI2) (hK := hK) (hloc := hloc)
    (hSC := _root_.MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth hI2) (hE := hE) (hFL :=
    hFL) (hBG := hBG) (hE1 := hE1) (hE2 := hE2) (hscale := hscale) (hND := hND)

end MatedCRT
end

section
open MeasureTheory Set Filter Topology Metric HarmonicBalls
namespace MatedCRT

/-- `firstPass_6_1_corrected` with the cluster strong compatibility binder (hSC) discharged from the
  volume growth input (Lemma 5.8, `MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth`,
  MatedCRT/FirstPass/Closure/HSCDerived.lean). The conclusion and every other binder are unchanged.
  -/
theorem firstPass_6_1_corrected_noSC
    (𝒮 : SpaceFillingSLEModel)
    (h610 : IterativeBoundStmt 𝒮)
    (h51 : IDLALowerBoundStmt 𝒮)
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hCentre : FrozenGreenBallCentre)
    (hGB : HarmonicBalls.GreenFunctionBallStmt)
    (hpole : FrozenGreenDiscPole)
    (hOpen : ClusterOpenLaplacianStmt.{0})
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw)
    (h27 : VolumeGrowthStmt)
    : IDLAUpperBoundStmt 𝒮 :=
  firstPass_6_1_corrected (𝒮 := 𝒮) (h610 := h610) (h51 := h51) (hU := hU) (hmeasT := hmeasT) (hstd
    := hstd) (hmin := hmin) (hCentre := hCentre) (hGB := hGB) (hpole := hpole) (hOpen := hOpen)
    (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hExist
    := hExist) (hThm11 := hThm11) (hProp56 := hProp56) (hconf := hconf) (hI2 := hI2) (hK := hK)
    (hloc := hloc) (hSC := _root_.MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth hI2) (hE
    := hE) (hFL := hFL) (h27 := h27)

end MatedCRT
end
