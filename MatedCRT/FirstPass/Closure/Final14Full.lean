import MatedCRT.FirstPass.Closure.Final14Composed
import MatedCRT.FirstPass.Closure.Final23

/-!
# Convergence results 1.4 and 1.6 from literature inputs

`closed_1_4_full` and `closed_1_6_full` are `closed_1_4_composed` and `closed_1_6_composed`
(`MatedCRT/FirstPass/Closure/Final14Composed.lean`) with the hypothesis `h23 : ConeHarmonicBallsStmt` replaced by
`closed_2_3_lit` (`MatedCRT/FirstPass/Closure/Final23.lean`). The binders of the two theorems are literature inputs:
Frozen statements, External statements, Proposed statements, Harmonic Balls Draft statements cited in the paper, and
the reference-model core `CertifiedReferenceModelCore`. The hypothesis `h22 : LQGMeasurePropertiesStmt` (Lemma 2.2) is
discharged by `closed_2_2_lit` from `hscale`, `hBG` and the binder `hND : LQGMeasureNonDyadicDilationPart`.
-/

namespace MatedCRT
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- **Internal DLA on mated-CRT maps, convergence (1.4), from literature inputs.** The conclusion is
`ConvergenceOfIDLAStmt 𝒮`, as for `closed_1_4_composed`. -/
theorem closed_1_4_full
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
    (hSC : FrozenClusterStrongCompatibility)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hBdryHB : ClusterBoundaryMeasureZeroStmt.{0})
    (hExistHB : ExistenceHarmonicBallsStmt.{0})
    (hProp56HB : UniquenessHarmonicBallsStmt.{0})
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0})
    (hlocHB : HarmonicBallLocalSetStmt.{0})
    (hSCHB : ClusterStrongCompatibilityStmt.{0})
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGB : HarmonicBalls.GreenFunctionBallStmt)
    (hpole : FrozenGreenDiscPole)

   : ConvergenceOfIDLAStmt 𝒮 :=
  MatedCRT.closed_1_4_composed (ν := ν) (hcore := hcore) (hscale := hscale) (hsc := hsc)
    (hrp := hrp) (hind := hind) (hEnvS := hEnvS) (hBG := hBG) (h0 := h0) (h2 := h2) (hV := hV)
    (h23 := closed_2_3_lit hBG hscale hND hstd hGBC h32 hSup hCons hMono hCompat hBdryHB hExistHB
    hThm11 hProp56HB hconf hI2HB hK hlocHB hSCHB hE hFL hE1 hE2 hU hmeasT hmin hGB hpole hrescale)
    (hdiv := hdiv) (hF3 := hF3) (hsup := hsup) (hmodel := hmodel) (hFL := hFL) (hstd := hstd)
    (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2)
    (h22 := closed_2_2_lit hscale hBG hND) (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82)
    (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat)
    (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc)
    (hSC := hSC) (hrescale := hrescale)

/-- **Divisible sandpile on mated-CRT maps, convergence (1.6), from literature inputs.** The conclusion is
`ConvergenceOfDivSandpileStmt 𝒮`, as for `closed_1_6_composed`. -/
theorem closed_1_6_full
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
    (hSC : FrozenClusterStrongCompatibility)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hBdryHB : ClusterBoundaryMeasureZeroStmt.{0})
    (hExistHB : ExistenceHarmonicBallsStmt.{0})
    (hProp56HB : UniquenessHarmonicBallsStmt.{0})
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0})
    (hlocHB : HarmonicBallLocalSetStmt.{0})
    (hSCHB : ClusterStrongCompatibilityStmt.{0})
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGB : HarmonicBalls.GreenFunctionBallStmt)
    (hpole : FrozenGreenDiscPole)

   : ConvergenceOfDivSandpileStmt 𝒮 :=
  MatedCRT.closed_1_6_composed (ν := ν) (hcore := hcore) (hscale := hscale) (hsc := hsc)
    (hrp := hrp) (hind := hind) (hEnvS := hEnvS) (hBG := hBG) (h0 := h0) (h2 := h2) (hV := hV)
    (h23 := closed_2_3_lit hBG hscale hND hstd hGBC h32 hSup hCons hMono hCompat hBdryHB hExistHB
    hThm11 hProp56HB hconf hI2HB hK hlocHB hSCHB hE hFL hE1 hE2 hU hmeasT hmin hGB hpole hrescale)
    (hdiv := hdiv) (hF3 := hF3) (hsup := hsup) (hmodel := hmodel) (hFL := hFL) (hstd := hstd)
    (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2)
    (h22 := closed_2_2_lit hscale hBG hND) (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82)
    (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat)
    (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc)
    (hSC := hSC) (hrescale := hrescale)

end MatedCRT
