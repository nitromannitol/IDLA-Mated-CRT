import MatedCRT.FirstPass.Closure.Final14Dedup
import MatedCRT.FirstPass.HBRewire
import MatedCRT.FirstPass.LPBridge.UniversalMeasurability
import MatedCRT.FirstPass.LPBridge.LQGTestIntegralMeasurable
import MatedCRT.FirstPass.LPBridge.MinimumPrinciples

/-!
# Convergence results 1.4 and 1.6 with the closure and LP-bridge binders discharged

`closed_1_4_lp` and `closed_1_6_lp` have the conclusions of `closed_1_4_dedup` and `closed_1_6_dedup`
(`MatedCRT/FirstPass/Closure/Final14Dedup.lean`), with eight of their 45 binders discharged by existing theorems:
* `hsc`, `hrp`, `hind` are the three conjuncts of `SLEModelClosureInput 𝒮` (`MatedCRT/FirstPass/SLERef/Extended.lean:39`),
  which is the second conjunct of `hcore : CertifiedReferenceModelCore ν 𝒮` (`MatedCRT/FirstPass/S5qe.lean:33`).
  They are supplied by the closure consumers `MatedCRT.scaleInvariance_of_closure`, `MatedCRT.reparametrization_of_closure`
  and `MatedCRT.indepMono_of_closure` (`Extended.lean:235`, `:240`, `:245`).
* `hGB : HarmonicBalls.GreenFunctionBallStmt` is `MatedCRT.HBRewire.GreenFunctionBallStmt_of_hb` (`MatedCRT/FirstPass/HBRewire.lean:34`),
  which is `HarmonicBalls.firstPass_2_3` and has no hypotheses.
* `hpole : FrozenGreenDiscPole` is `MatedCRT.HBRewire.FrozenGreenDiscPole_of_hb` (`HBRewire.lean:41`), with no hypotheses.
* `hU : FrozenUniversalMeasurabilityOfAnalytic` is `frozenUniversalMeasurabilityOfAnalytic_holds`
  (`MatedCRT/FirstPass/LPBridge/UniversalMeasurability.lean:18`), from `LatticeProb.AnalyticSet.nullMeasurableSet`.
* `hmeasT : FrozenLQGTestIntegralMeasurable` is `frozenLQGTestIntegralMeasurable_holds`
  (`MatedCRT/FirstPass/LPBridge/LQGTestIntegralMeasurable.lean:49`).
* `hmin : FrozenSuperharmonicMinimumPrinciple` is `frozenSuperharmonicMinimumPrinciple_holds`
  (`MatedCRT/FirstPass/LPBridge/MinimumPrinciples.lean:22`).

The remaining binders are those of `closed_1_4_dedup` and `closed_1_6_dedup`; the proofs are applications of them.
-/

namespace MatedCRT
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- **Internal DLA on mated-CRT maps, convergence (1.4), with the closure and LP-bridge binders discharged.**
The conclusion is `ConvergenceOfIDLAStmt 𝒮`, as for `closed_1_4_dedup`. -/
theorem closed_1_4_lp
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
    (hlocHB : HarmonicBallLocalSetStmt.{0})
    (hSCHB : ClusterStrongCompatibilityStmt.{0}) :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_dedup (ν := ν) (hcore := hcore) (hscale := hscale)
    (hsc := scaleInvariance_of_closure hcore.2.1) (hrp := reparametrization_of_closure hcore.2.1)
    (hind := indepMono_of_closure hcore.2.1) (hEnvS := hEnvS) (hBG := hBG) (h0 := h0) (h2 := h2)
    (hV := hV) (hdiv := hdiv) (hF3 := hF3) (hsup := hsup) (hFL := hFL) (hstd := hstd) (hGBC := hGBC)
    (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (hG15 := hG15) (h32 := h32)
    (h611 := h611) (h82 := h82) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat)
    (hThm11 := hThm11) (hrescale := hrescale) (hND := hND) (hBdryHB := hBdryHB) (hExistHB := hExistHB)
    (hProp56HB := hProp56HB) (hI2HB := hI2HB) (hlocHB := hlocHB) (hSCHB := hSCHB)
    (hU := frozenUniversalMeasurabilityOfAnalytic_holds) (hmeasT := frozenLQGTestIntegralMeasurable_holds)
    (hmin := frozenSuperharmonicMinimumPrinciple_holds) (hGB := HBRewire.GreenFunctionBallStmt_of_hb)
    (hpole := HBRewire.FrozenGreenDiscPole_of_hb)

/-- **Divisible sandpile on mated-CRT maps, convergence (1.6), with the closure and LP-bridge binders discharged.**
The conclusion is `ConvergenceOfDivSandpileStmt 𝒮`, as for `closed_1_6_dedup`. The binders discharged are those of
`closed_1_4_lp`. -/
theorem closed_1_6_lp
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
    (hlocHB : HarmonicBallLocalSetStmt.{0})
    (hSCHB : ClusterStrongCompatibilityStmt.{0}) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_dedup (ν := ν) (hcore := hcore) (hscale := hscale)
    (hsc := scaleInvariance_of_closure hcore.2.1) (hrp := reparametrization_of_closure hcore.2.1)
    (hind := indepMono_of_closure hcore.2.1) (hEnvS := hEnvS) (hBG := hBG) (h0 := h0) (h2 := h2)
    (hV := hV) (hdiv := hdiv) (hF3 := hF3) (hsup := hsup) (hFL := hFL) (hstd := hstd) (hGBC := hGBC)
    (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (hG15 := hG15) (h32 := h32)
    (h611 := h611) (h82 := h82) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat)
    (hThm11 := hThm11) (hrescale := hrescale) (hND := hND) (hBdryHB := hBdryHB) (hExistHB := hExistHB)
    (hProp56HB := hProp56HB) (hI2HB := hI2HB) (hlocHB := hlocHB) (hSCHB := hSCHB)
    (hU := frozenUniversalMeasurabilityOfAnalytic_holds) (hmeasT := frozenLQGTestIntegralMeasurable_holds)
    (hmin := frozenSuperharmonicMinimumPrinciple_holds) (hGB := HBRewire.GreenFunctionBallStmt_of_hb)
    (hpole := HBRewire.FrozenGreenDiscPole_of_hb)

end MatedCRT

#print axioms MatedCRT.closed_1_4_lp
#print axioms MatedCRT.closed_1_6_lp
