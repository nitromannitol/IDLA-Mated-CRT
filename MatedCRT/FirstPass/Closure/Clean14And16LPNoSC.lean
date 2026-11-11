import MatedCRT.FirstPass.Closure.Final14LP
import MatedCRT.FirstPass.Closure.HSCDerived

/-!
# Convergence results 1.4 and 1.6, LP-bridge form with the cluster strong compatibility binder discharged

`closed_1_4_lp_noSC` and `closed_1_6_lp_noSC` have the conclusions of `closed_1_4_lp` (`Final14LP.lean:35`) and
`closed_1_6_lp` (`Final14LP.lean:89`), and the same binders except the last one: the cluster strong compatibility
binder `hSCHB : ClusterStrongCompatibilityStmt.{0}` is removed. It is supplied by
`MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth hI2HB` (`FirstPass/Closure/HSCDerived.lean:19`), from the
all-scales volume growth input `hI2HB : LQGVolumeGrowthAllScalesStmt.{0}`, which is already a binder of both theorems.
This is Lemma 5.8 (cluster strong compatibility) of the Harmonic-Balls paper, derived from the all-scales volume growth
estimate, as in `closed_1_4_full_noSC` and `closed_1_6_full_noSC` (`FirstPass/Closure/HSCRewire.lean:30` and `:98`).
-/

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

namespace MatedCRT

/-- **Internal DLA on mated-CRT maps, convergence (1.4), LP-bridge form with the cluster strong compatibility binder
discharged from the volume growth input.** The conclusion is `ConvergenceOfIDLAStmt 𝒮`, as for `closed_1_4_lp`; the
binders are those of `closed_1_4_lp` without `hSCHB`. -/
theorem closed_1_4_lp_noSC
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
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
    (hlocHB : HarmonicBallLocalSetStmt.{0}) :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_lp (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hscale := hscale) (hEnvS := hEnvS) (hBG := hBG)
    (h0 := h0) (h2 := h2) (hV := hV) (hdiv := hdiv) (hF3 := hF3) (hsup := hsup) (hFL := hFL)
    (hstd := hstd) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2)
    (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82) (hSup := hSup) (hCons := hCons)
    (hMono := hMono) (hCompat := hCompat) (hThm11 := hThm11) (hrescale := hrescale) (hND := hND)
    (hBdryHB := hBdryHB) (hExistHB := hExistHB) (hProp56HB := hProp56HB) (hI2HB := hI2HB)
    (hlocHB := hlocHB) (hSCHB := frozenClusterStrongCompatibility_of_volumeGrowth hI2HB)

/-- **Divisible sandpile on mated-CRT maps, convergence (1.6), LP-bridge form with the cluster strong compatibility
binder discharged from the volume growth input.** The conclusion is `ConvergenceOfDivSandpileStmt 𝒮`, as for
`closed_1_6_lp`; the binders are those of `closed_1_6_lp` without `hSCHB`. -/
theorem closed_1_6_lp_noSC
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
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
    (hlocHB : HarmonicBallLocalSetStmt.{0}) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_lp (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hscale := hscale) (hEnvS := hEnvS) (hBG := hBG)
    (h0 := h0) (h2 := h2) (hV := hV) (hdiv := hdiv) (hF3 := hF3) (hsup := hsup) (hFL := hFL)
    (hstd := hstd) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2)
    (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82) (hSup := hSup) (hCons := hCons)
    (hMono := hMono) (hCompat := hCompat) (hThm11 := hThm11) (hrescale := hrescale) (hND := hND)
    (hBdryHB := hBdryHB) (hExistHB := hExistHB) (hProp56HB := hProp56HB) (hI2HB := hI2HB)
    (hlocHB := hlocHB) (hSCHB := frozenClusterStrongCompatibility_of_volumeGrowth hI2HB)

end MatedCRT

#print axioms MatedCRT.closed_1_4_lp_noSC
#print axioms MatedCRT.closed_1_6_lp_noSC
