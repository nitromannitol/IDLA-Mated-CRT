import MatedCRT.FirstPass.Closure.Final14Full
import MatedCRT.FirstPass.S2m

/-!
# Convergence results 1.4 and 1.6 with duplicated binders removed

`closed_1_4_dedup` and `closed_1_6_dedup` have the conclusions of `closed_1_4_full` and `closed_1_6_full`
(`MatedCRT/FirstPass/Closure/Final14Full.lean`), with seven of their 52 binders removed. Each removed binder is
either a definitional copy of a Harmonic Balls Draft statement that is kept, or a proposition that follows from a
kept binder by an existing theorem. Each removed binder is supplied in the proof by the definition or by that theorem.
The removal therefore changes no content: the full versions' extra hypotheses are consequences of the kept ones.

The removed binders and their sources:
* `hBdry : FrozenClusterBoundaryMeasureZero` is `ClusterBoundaryMeasureZeroStmt.{0}` (`MatedCRT/FirstPass/Frozen/S5Cited.lean:54`);
  kept: `hBdryHB`.
* `hEx : FrozenExistenceHarmonicBalls` is `ExistenceHarmonicBallsStmt.{0}` (`S5Cited.lean:59`); kept: `hExistHB`.
* `hProp56 : FrozenUniquenessHarmonicBalls` is `UniquenessHarmonicBallsStmt.{0}` (`S5Cited.lean:64`); kept: `hProp56HB`.
* `hloc : FrozenHarmonicBallLocalSet` is `HarmonicBallLocalSetStmt.{0}` (`S5Cited.lean:69`); kept: `hlocHB`.
* `hSC : FrozenClusterStrongCompatibility` is `ClusterStrongCompatibilityStmt.{0}` (`S5Cited.lean:74`); kept: `hSCHB`.
* `hI2 : FrozenLQGVolumeGrowthAllScales` is `LQGVolumeGrowthAllScalesStmt.{0}` (`S5Cited.lean:39`); kept: `hI2HB`.
* `hmodel : FPWholePlaneLQGModel` is `WholePlaneLQGModelStep`, and `firstPass_wholePlaneLQGModel_of_existence`
  (`MatedCRT/FirstPass/S2m.lean:26`) derives it from the kept binder `hE : FrozenLQGMeasureExistenceInsertion`.

The kept Harmonic Balls Draft statements are the results of the Harmonic-Balls paper (arXiv:2208.11795) that the paper
cites. The conclusions are those of `closed_1_4_full` and `closed_1_6_full`; the proofs are applications of them.
-/

namespace MatedCRT
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- **Internal DLA on mated-CRT maps, convergence (1.4), with duplicated binders removed.** The conclusion is
`ConvergenceOfIDLAStmt 𝒮`, as for `closed_1_4_full`. The binders `hBdry`, `hEx`, `hProp56`, `hloc`, `hSC`, `hI2` and
`hmodel` of `closed_1_4_full` are supplied from `hBdryHB`, `hExistHB`, `hProp56HB`, `hlocHB`, `hSCHB`, `hI2HB` and
`hE`. -/
theorem closed_1_4_dedup
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
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
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
    (hpole : FrozenGreenDiscPole) :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_full (ν := ν) (hcore := hcore) (hscale := hscale) (hsc := hsc) (hrp := hrp) (hind := hind)
    (hEnvS := hEnvS) (hBG := hBG) (h0 := h0) (h2 := h2) (hV := hV) (hdiv := hdiv) (hF3 := hF3)
    (hsup := hsup) (hmodel := FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence hE)
    (hFL := hFL) (hstd := hstd) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE)
    (hE1 := hE1) (hE2 := hE2) (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82)
    (hI2 := hI2HB) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat)
    (hBdry := hBdryHB) (hEx := hExistHB) (hThm11 := hThm11) (hProp56 := hProp56HB) (hloc := hlocHB)
    (hSC := hSCHB) (hrescale := hrescale) (hND := hND) (hBdryHB := hBdryHB) (hExistHB := hExistHB)
    (hProp56HB := hProp56HB) (hI2HB := hI2HB) (hlocHB := hlocHB) (hSCHB := hSCHB) (hU := hU)
    (hmeasT := hmeasT) (hmin := hmin) (hGB := hGB) (hpole := hpole)

/-- **Divisible sandpile on mated-CRT maps, convergence (1.6), with duplicated binders removed.** The conclusion is
`ConvergenceOfDivSandpileStmt 𝒮`, as for `closed_1_6_full`. The binders removed and their replacements are those of
`closed_1_4_dedup`. -/
theorem closed_1_6_dedup
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
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
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
    (hpole : FrozenGreenDiscPole) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_full (ν := ν) (hcore := hcore) (hscale := hscale) (hsc := hsc) (hrp := hrp) (hind := hind)
    (hEnvS := hEnvS) (hBG := hBG) (h0 := h0) (h2 := h2) (hV := hV) (hdiv := hdiv) (hF3 := hF3)
    (hsup := hsup) (hmodel := FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence hE)
    (hFL := hFL) (hstd := hstd) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE)
    (hE1 := hE1) (hE2 := hE2) (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82)
    (hI2 := hI2HB) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat)
    (hBdry := hBdryHB) (hEx := hExistHB) (hThm11 := hThm11) (hProp56 := hProp56HB) (hloc := hlocHB)
    (hSC := hSCHB) (hrescale := hrescale) (hND := hND) (hBdryHB := hBdryHB) (hExistHB := hExistHB)
    (hProp56HB := hProp56HB) (hI2HB := hI2HB) (hlocHB := hlocHB) (hSCHB := hSCHB) (hU := hU)
    (hmeasT := hmeasT) (hmin := hmin) (hGB := hGB) (hpole := hpole)

end MatedCRT
