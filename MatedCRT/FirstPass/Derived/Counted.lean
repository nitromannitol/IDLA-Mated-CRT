import HarmonicBalls.Assembly.ExistenceUniqueness
import HarmonicBalls.FirstPass.S2S3S4S9SA
import HarmonicBalls.Proofs.Sec3.Basic
import HarmonicBalls.Proofs.Sec3.ClusterCompatibility
import HarmonicBalls.Proofs.Sec3.ConservationOfMassLemma
import HarmonicBalls.Proofs.Sec3.OpenLaplacian
import HarmonicBalls.Proofs.Sec5.StrongCompatibilityAssembly
import HarmonicBalls.Proofs.Sec6.VolumeGrowthConsequences
import MatedCRT.Audit.StatementsSec3Sec5M1
import MatedCRT.FirstPass.Closure.AuditRewire14
import MatedCRT.FirstPass.Closure.Clean2xLP
import MatedCRT.FirstPass.Closure.Clean42And5LP
import MatedCRT.FirstPass.Closure.Clean61And71LP
import MatedCRT.FirstPass.Closure.CleanSec23LP
import MatedCRT.FirstPass.Closure.CleanSec23LPUniform
import MatedCRT.FirstPass.Closure.CleanSec456LP
import MatedCRT.FirstPass.Closure.HLsRewire53
import MatedCRT.FirstPass.Closure.LssDerived
import MatedCRT.FirstPass.Closure.OwnBinderRewire
import MatedCRT.FirstPass.Closure.Section3
import MatedCRT.FirstPass.Closure.Steps42
import MatedCRT.FirstPass.Derived.ConeCircleLawUnique
import MatedCRT.FirstPass.Derived.ConeDilationRatioHolds
import MatedCRT.FirstPass.Derived.ConeLogLocalCodeLawStdDerived
import MatedCRT.FirstPass.Derived.ConeRadialDivergence
import MatedCRT.FirstPass.Derived.ConeReferenceExistsDerived
import MatedCRT.FirstPass.Derived.ConeWholePlaneFieldLaw
import MatedCRT.FirstPass.Derived.CoordChangeZero
import MatedCRT.FirstPass.Derived.DiscGreenCentre
import MatedCRT.FirstPass.Derived.HarmonicBallsVolumeGrowth
import MatedCRT.FirstPass.Derived.InsertionCoordinateRule
import MatedCRT.FirstPass.Derived.LQGMeasureInputs
import MatedCRT.FirstPass.Derived.UpperVolumeTail
import MatedCRT.FirstPass.HBRewire
import MatedCRT.FirstPass.LIClosed68Y
import MatedCRT.FirstPass.LPBridge.LQGTestIntegralMeasurable
import MatedCRT.FirstPass.LPBridge.MinimumPrinciples
import MatedCRT.FirstPass.LPBridge.UniversalMeasurability
import MatedCRT.FirstPass.Phase2Rewire
import MatedCRT.FirstPass.S2g.Canonical
import MatedCRT.FirstPass.S2g.CanonicalGate
import MatedCRT.FirstPass.S2g.Draft24
import MatedCRT.FirstPass.S2g.HalfBallGood
import MatedCRT.FirstPass.S2g.MomentSeparation
import MatedCRT.FirstPass.S2g.SourcePathwise
import MatedCRT.FirstPass.S2i.CanonicalFactor
import MatedCRT.FirstPass.S2m
import MatedCRT.FirstPass.S2y.ConeCircleAbsApprox
import MatedCRT.FirstPass.S2y.LateralAssembly250
import MatedCRT.FirstPass.S4d.HorizonUnique
import MatedCRT.FirstPass.S4d.ScaleBridge
import MatedCRT.FirstPass.S6q
import MatedCRT.FirstPass.SLERef.Certified
import MatedCRT.Proofs.Sec1.ConeScaleRadius
import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.RadialContainment
import MatedCRT.Proofs.Sec2.LQGMeasureProperties.Main
import MatedCRT.Proofs.Sec2.LQGMeasureProperties.NonAtomicScaling
import MatedCRT.Proofs.Sec3.ConeBallMass
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.AlmostSureInterior

/-!
# Counted theorems with their derivable inputs supplied

For each counted theorem of the paper, every hypothesis which follows from the other hypotheses of the same
theorem by theorems of this repository and of the Harmonic-Balls package is supplied: the wrapper
`<name>_derivedInputs` has the same conclusion and the remaining binders. No binder is added. The counted
theorems and the frozen statements are unchanged. Each `have` line is one theorem applied to remaining
binders and to earlier lines.

This file is generated from the signatures of the counted theorems; do not edit by hand.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_1_4_lp_noSC_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with the inputs supplied which follow from its other inputs: `h0 : FPWholePlaneLQGExistence` by `MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `h2 : FPWholePlaneLQGCoordinateChange` by `MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`, `hV : FPWholePlaneUpperVolumeTail` by `MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds`, `hdiv : FrozenConeRadialDivergenceCorrected` by `MatedCRT.frozenConeRadialDivergenceCorrected_holds`, `hF3 : FrozenDiskGreenNonnegCont` by `MatedCRT.frozenDiskGreenNonnegCont_holds`, `h27 : VolumeGrowthStmt` by `MatedCRT.volumeGrowthStmt_of_berestyckiGwynne`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `h611 : FrozenVeryGoodAnnulusHarnackType` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hND : LQGMeasureNonDyadicDilationPart` by `MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds`, `hBdryHB : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint`, `hProp56HB : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_1_4_lp_noSC_noSup_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hconf : FrozenHBInitialConfinement)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    (hExistHB : ExistenceHarmonicBallsStmt.{0})
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0})
    (hlocHB : HarmonicBallLocalSetStmt.{0}) :
    ConvergenceOfIDLAStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d3 := MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d6 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d7 := MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds
  have d8 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d9 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  have d10 := MatedCRT.coneCircleLawUniqueStep_holds
  have d11 := MatedCRT.frozenConeRadialDivergenceCorrected_holds
  have d12 := MatedCRT.frozenDiskGreenNonnegCont_holds
  have d13 := MatedCRT.frozenGreenBallCentre_holds
  have d14 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only (hI2 := hI2HB)
  have d15 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2HB)
  have d16 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2HB)
  have d17 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2HB)
  have d18 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2HB)
  have d19 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2HB)
  have d20 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2HB)
  have d21 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d22 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExistHB) (h56 := d20)
  have d23 := MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint (hI2 := hI2HB) (h82 := h82)
  closed_1_4_lp_noSC_noSup (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hscale := hscale) (hEnvS := hEnvS) (hBG := hBG)
    (h0 := d9) (h2 := d8) (hV := d3) (hdiv := d11) (hF3 := d12) (h27 := d21) (hFL := d1) (hstd := d4) (hGBC := d13)
    (hconf := hconf) (hK := d5) (hE := d6) (hE1 := d10) (hE2 := d2) (hG15 := hG15) (h32 := d18) (h611 := d14)
    (h82 := h82) (hSup := d19) (hCons := d16) (hMono := d17) (hCompat := d15) (hThm11 := d22) (hrescale := hrescale)
    (hND := d7) (hBdryHB := d23) (hExistHB := hExistHB) (hProp56HB := d20) (hI2HB := hI2HB) (hlocHB := hlocHB)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_1_6_lp_noSC_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with the inputs supplied which follow from its other inputs: `h0 : FPWholePlaneLQGExistence` by `MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `h2 : FPWholePlaneLQGCoordinateChange` by `MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`, `hV : FPWholePlaneUpperVolumeTail` by `MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds`, `hdiv : FrozenConeRadialDivergenceCorrected` by `MatedCRT.frozenConeRadialDivergenceCorrected_holds`, `hF3 : FrozenDiskGreenNonnegCont` by `MatedCRT.frozenDiskGreenNonnegCont_holds`, `h27 : VolumeGrowthStmt` by `MatedCRT.volumeGrowthStmt_of_berestyckiGwynne`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `h611 : FrozenVeryGoodAnnulusHarnackType` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hND : LQGMeasureNonDyadicDilationPart` by `MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds`, `hBdryHB : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint`, `hProp56HB : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_1_6_lp_noSC_noSup_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hconf : FrozenHBInitialConfinement)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    (hExistHB : ExistenceHarmonicBallsStmt.{0})
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0})
    (hlocHB : HarmonicBallLocalSetStmt.{0}) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d3 := MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d6 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d7 := MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds
  have d8 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d9 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  have d10 := MatedCRT.coneCircleLawUniqueStep_holds
  have d11 := MatedCRT.frozenConeRadialDivergenceCorrected_holds
  have d12 := MatedCRT.frozenDiskGreenNonnegCont_holds
  have d13 := MatedCRT.frozenGreenBallCentre_holds
  have d14 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only (hI2 := hI2HB)
  have d15 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2HB)
  have d16 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2HB)
  have d17 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2HB)
  have d18 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2HB)
  have d19 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2HB)
  have d20 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2HB)
  have d21 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d22 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExistHB) (h56 := d20)
  have d23 := MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint (hI2 := hI2HB) (h82 := h82)
  closed_1_6_lp_noSC_noSup (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hscale := hscale) (hEnvS := hEnvS) (hBG := hBG)
    (h0 := d9) (h2 := d8) (hV := d3) (hdiv := d11) (hF3 := d12) (h27 := d21) (hFL := d1) (hstd := d4) (hGBC := d13)
    (hconf := hconf) (hK := d5) (hE := d6) (hE1 := d10) (hE2 := d2) (hG15 := hG15) (h32 := d18) (h611 := d14)
    (h82 := h82) (hSup := d19) (hCons := d16) (hMono := d17) (hCompat := d15) (hThm11 := d22) (hrescale := hrescale)
    (hND := d7) (hBdryHB := d23) (hExistHB := hExistHB) (hProp56HB := d20) (hI2HB := hI2HB) (hlocHB := hlocHB)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_2_3_lp` (MatedCRT/FirstPass/Closure/Clean2xLP.lean) with the inputs supplied which follow from its other inputs: `hND : LQGMeasureNonDyadicDilationPart` by `MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds`, `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56HB : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_2_3_lp_derivedInputs
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hscale : QuantumConeScalingInput)
    (hBdryHB : ClusterBoundaryMeasureZeroStmt.{0})
    (hExistHB : ExistenceHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0})
    (hlocHB : HarmonicBallLocalSetStmt.{0})
    (hrescale : ConeRescaledMeasureIsConeFieldInput) :
    ConeHarmonicBallsStmt :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d3 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d6 := MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds
  have d7 := MatedCRT.coneCircleLawUniqueStep_holds
  have d8 := MatedCRT.frozenGreenBallCentre_holds
  have d9 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2HB)
  have d10 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2HB)
  have d11 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2HB)
  have d12 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2HB)
  have d13 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2HB)
  have d14 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2HB)
  have d15 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExistHB) (h56 := d14)
  closed_2_3_lp (hBG := hBG) (hscale := hscale) (hND := d6) (hstd := d3) (hGBC := d8) (h32 := d12) (hSup := d13)
    (hCons := d10) (hMono := d11) (hCompat := d9) (hBdryHB := hBdryHB) (hExistHB := hExistHB) (hThm11 := d15)
    (hProp56HB := d14) (hconf := hconf) (hI2HB := hI2HB) (hK := d4) (hlocHB := hlocHB) (hE := d5) (hFL := d1)
    (hE1 := d7) (hE2 := d2) (hrescale := hrescale)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_2_4_lp` (MatedCRT/FirstPass/Closure/Clean2xLP.lean) with the inputs supplied which follow from its other inputs: `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_2_4_lp_derivedInputs
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    ConeHarmonicBallsUpToFixedTimeCanonicalStmt :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d3 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d5 := MatedCRT.frozenGreenBallCentre_holds
  have d6 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d7 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d8 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d9 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d10 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d11 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d12 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d11)
  closed_2_4_lp (hstd := d2) (hCentre := d5) (hOpen := d9) (hSup := d10) (hCons := d7) (hMono := d8) (hCompat := d6)
    (hBdry := hBdry) (hExist := hExist) (hThm11 := d12) (hProp56 := d11) (hconf := hconf) (hI2 := hI2) (hK := d3)
    (hloc := hloc) (hE := d4) (hFL := d1) (hBG := hBG)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_2_5_lp` (MatedCRT/FirstPass/Closure/Clean2xLP.lean) with the inputs supplied which follow from its other inputs: `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`, `hND : LQGMeasureNonDyadicDilationPart` by `MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_2_5_lp_derivedInputs
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hscale : QuantumConeScalingInput) :
    ConeScaleInvarianceUpToFixedTimeCanonicalStmt :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d3 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d6 := MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds
  have d7 := MatedCRT.coneCircleLawUniqueStep_holds
  have d8 := MatedCRT.frozenGreenBallCentre_holds
  have d9 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d10 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d11 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d12 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d13 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d14 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d15 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d14)
  closed_2_5_lp (hstd := d3) (hCentre := d8) (hOpen := d12) (hSup := d13) (hCons := d10) (hMono := d11)
    (hCompat := d9) (hBdry := hBdry) (hExist := hExist) (hThm11 := d15) (hProp56 := d14) (hconf := hconf) (hI2 := hI2)
    (hK := d4) (hloc := hloc) (hE := d5) (hFL := d1) (hBG := hBG) (hE1 := d7) (hE2 := d2) (hscale := hscale)
    (hND := d6)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_2_6_lp` (MatedCRT/FirstPass/Closure/Clean2xLP.lean) with the inputs supplied which follow from its other inputs: `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`, `hND : LQGMeasureNonDyadicDilationPart` by `MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_2_6_lp_derivedInputs
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hscale : QuantumConeScalingInput) :
    ConeScaleInvarianceStmt :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d3 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d6 := MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds
  have d7 := MatedCRT.coneCircleLawUniqueStep_holds
  have d8 := MatedCRT.frozenGreenBallCentre_holds
  have d9 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d10 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d11 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d12 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d13 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d14 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d15 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d14)
  closed_2_6_lp (hstd := d3) (hCentre := d8) (hOpen := d12) (hSup := d13) (hCons := d10) (hMono := d11)
    (hCompat := d9) (hBdry := hBdry) (hExist := hExist) (hThm11 := d15) (hProp56 := d14) (hconf := hconf) (hI2 := hI2)
    (hK := d4) (hloc := hloc) (hE := d5) (hFL := d1) (hBG := hBG) (hE1 := d7) (hE2 := d2) (hscale := hscale)
    (hND := d6)

end MatedCRT

namespace MatedCRT

open MeasureTheory

open MatedCRT.FirstPass36 in
/-- The counted theorem `MatedCRT.closed_3_6_lp_uniform` (MatedCRT/FirstPass/Closure/CleanSec23LPUniform.lean) with the inputs supplied which follow from its other inputs: `_hm : MepsScalingInput 𝒮` by `MatedCRT.CertifiedReferenceModel.mepsScaling`, `_h32 : FrozenDiscreteHolderContinuityCorrected 𝒮` by `MatedCRT.CertifiedReferenceModel.frozenDiscreteHolderContinuityCorrected`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_3_6_lp_uniform_derivedInputs
    (𝒮 : SpaceFillingSLEModel)
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hBE : FrozenOneSidedBoundaryContinuityFlooredUniform 𝒮) :
    CorrectedHarmonicConvergenceStmt 𝒮 ∧ CorrectedHarmonicSameWalkAnnealedStmt 𝒮 :=
  have d1 := MatedCRT.CertifiedReferenceModel.frozenDiscreteHolderContinuityCorrected (h := hC)
  have d2 := MatedCRT.CertifiedReferenceModel.mepsScaling (h := hC)
  closed_3_6_lp_uniform (𝒮 := 𝒮) (ν := ν) (hC := hC) (_hm := d2) (_h32 := d1) (hBE := hBE)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_3_7_lp` (MatedCRT/FirstPass/Closure/CleanSec23LP.lean) with the inputs supplied which follow from its other inputs: `hm : MepsScalingInput 𝒮` by `MatedCRT.CertifiedReferenceModel.mepsScaling`, `h32 : FrozenDiscreteHolderContinuityCorrected 𝒮` by `MatedCRT.CertifiedReferenceModel.frozenDiscreteHolderContinuityCorrected`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_3_7_lp_derivedInputs
    (𝒮 : SpaceFillingSLEModel)
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    ConvergenceNormalizedExitTimeStmt 𝒮 :=
  have d1 := MatedCRT.CertifiedReferenceModel.frozenDiscreteHolderContinuityCorrected (h := hC)
  have d2 := MatedCRT.CertifiedReferenceModel.mepsScaling (h := hC)
  closed_3_7_lp (𝒮 := 𝒮) (ν := ν) (hC := hC) (hBG := hBG) (hm := d2) (h32 := d1)

end MatedCRT

namespace MatedCRT.FirstPassClosure

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.FirstPassClosure.closed_4_2_lp` (MatedCRT/FirstPass/Closure/Clean42And5LP.lean) with the inputs supplied which follow from its other inputs: `h23 : ConeHarmonicBallsStmt` by `MatedCRT.coneHarmonicBalls_of_numbered_results`, `h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt` by `MatedCRT.coneHarmonicBallsUpToFixedTimeCorrected_of_canonical`, `h33 : UniformConvergenceGreenKernelStmt 𝒮` by `MatedCRT.Audit.StatementsSec3Sec5M1.three_three_final_reduction`, `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`, `hND : LQGMeasureNonDyadicDilationPart` by `MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_4_2_lp_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮)
    (h35c : DiscreteDirichletProblemCorrectedStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (hcone : FrozenConeScalingLaw 𝒮)
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hscale : QuantumConeScalingInput)
    (hrescale : ConeRescaledMeasureIsConeFieldInput) :
    DivSandpileLowerBoundStmt 𝒮 :=
  have d1 := HarmonicBalls.firstPass_2_3
  have d2 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d3 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d6 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d7 := MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds
  have d8 := MatedCRT.HBRewire.FrozenGreenDiscPole_of_hb
  have d9 := MatedCRT.coneCircleAverageLocalityStep_proved
  have d10 := MatedCRT.coneCircleLawUniqueStep_holds
  have d11 := MatedCRT.frozenGreenBallCentre_holds
  have d12 := MatedCRT.frozenLQGTestIntegralMeasurable_holds
  have d13 := MatedCRT.frozenSuperharmonicMinimumPrinciple_holds
  have d14 := MatedCRT.frozenUniversalMeasurabilityOfAnalytic_holds
  have d15 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d16 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d17 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d18 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d19 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d20 := MatedCRT.LQGMeasure.coneFieldScalingStep_proved_radial (hscale := hscale)
  have d21 := MatedCRT.LQGMeasure.lqgMeasureDilationCovariancePart_of_nonDyadic (hND := d7)
  have d22 := MatedCRT.coneScaleRadiusPosStep_of_input (hscale := hscale)
  have d23 := MatedCRT.firstPass_2_17_ownBinders (hBG := hBG)
  have d24 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d25 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d26 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d24)
  have d27 := MatedCRT.LQGMeasure.coneLQGScalingStep_of_dilation (hIV := d21) (hpos := d22)
  have d28 := MatedCRT.LQGMeasure.lqgMeasureNonAtomicPart_of_scaling (h27 := d25) (hfield := d20) (hlqg := d27)
  have d29 := MatedCRT.LQGMeasure.lqgMeasureProperties_of_citedInputs (hNA := d28) (hCL := d9) (hND := d7)
  have d30 := MatedCRT.discretePotentialTightnessAeStep_of_inputs (hm := hm) (h217 := d23) (h218 := h218) (hH := hH)
  have d31 := MatedCRT.Audit.StatementsSec3Sec5M1.three_three_final_reduction (𝒮 := 𝒮) (h210 := h210) (h34 := h34)
    (h214 := h214) (h28 := h28) (hAe := d30)
  have d32 := MatedCRT.FirstPassClosure.coneHalfBallClosureInsideStep_proof (hI2 := hI2) (hK := d5) (hloc := hloc)
    (hEx := hExist) (hE := d6) (hFL := d2) (hBG := hBG)
  have d33 := MatedCRT.sourceHalfBallPathwiseStep_of_draft (hOpen := d18) (hSup := d19) (hCons := d16) (hMono := d17)
    (hCompat := d15) (hBdry := hBdry) (hExist := hExist) (hThm11 := d26) (hProp56 := d24) (hconf := hconf)
  have d34 := MatedCRT.coneHalfBallGood_of_source_sep (hU := d14) (hmeasT := d12) (hsrc := d33) (hstd := d4)
  have d35 := MatedCRT.coneCanonicalHalfBallStep_of_good (hgood := d34) (hmin := d13) (hC := d11) (hGB := d1)
    (hpole := d8)
  have d36 := MatedCRT.firstPass_2_4_canonical_of_inputs (hU := d14) (hmeasT := d12) (hsrc := d33) (hstd := d4)
    (hmin := d13) (hC := d11) (hGB := d1) (hpole := d8) (hcl := d32) (h27 := d25)
  have d37 := MatedCRT.coneHarmonicBallsUpToFixedTimeCorrected_of_canonical (h := d36)
  have d38 := MatedCRT.coneHarmonicBallsUpToFixedTimeStmt_of_canonical (hcan := d35) (hcl := d32)
  have d39 := MatedCRT.coneRescaledHalfBallHorizonUnique_fp (hcan := d35) (hcl := d32) (hrescale := hrescale)
  have d40 := MatedCRT.coneCanonicalFactor_proved (hcan := d35) (hcl := d32) (h27 := d25) (hE1 := d10) (hE2 := d3)
  have d41 := MatedCRT.firstPass_2_5_canonical_of_factor (hfac := d40) (hscale := hscale) (h22 := d29)
  have d42 := MatedCRT.coneScaleInvarianceUpToFixedTimeStmt_of_canonical (hcan := d35) (hcl := d32) (hc25 := d41)
    (hU := d39)
  have d43 := MatedCRT.coneHarmonicBalls_of_numbered_results (h24 := d38) (h25 := d42) (h27 := d25) (hscale := hscale)
    (h22 := d29)
  closed_4_2_lp (𝒮 := 𝒮) (hm := hm) (h210 := h210) (h34 := h34) (h214 := h214) (h28 := h28) (h35c := h35c)
    (h218 := h218) (hH := hH) (hcone := hcone) (h23 := d43) (h24c := d37) (h33 := d31) (hstd := d4) (hCentre := d11)
    (hOpen := d18) (hSup := d19) (hCons := d16) (hMono := d17) (hCompat := d15) (hBdry := hBdry) (hExist := hExist)
    (hThm11 := d26) (hProp56 := d24) (hconf := hconf) (hI2 := hI2) (hK := d5) (hloc := hloc) (hE := d6) (hFL := d2)
    (hBG := hBG) (hE1 := d10) (hE2 := d3) (hscale := hscale) (hND := d7) (hrescale := hrescale)

end MatedCRT.FirstPassClosure

namespace MatedCRT.FirstPassClosure

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.FirstPassClosure.closed_5_1_lp_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with the inputs supplied which follow from its other inputs: `h27 : VolumeGrowthStmt` by `MatedCRT.volumeGrowthStmt_of_berestyckiGwynne`, `hmodel : FPWholePlaneLQGModel` by `MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`, `hND : LQGMeasureNonDyadicDilationPart` by `MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `h611 : VeryGoodAnnulusHarnackTypeStmt.{0}` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hBdry : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hSC : ClusterStrongCompatibilityStmt.{0}` by `HarmonicBalls.clusterStrongCompatibilityStmt_of_volumeGrowth`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_5_1_lp_noSup_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hconf : FrozenHBInitialConfinement)
    (hscale : QuantumConeScalingInput)
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
    (h82 : TypicalPointManyGoodScalesStmt.{0})
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hEx : ExistenceHarmonicBallsStmt.{0})
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    IDLALowerBoundStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d3 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d6 := MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds
  have d7 := MatedCRT.coneCircleLawUniqueStep_holds
  have d8 := MatedCRT.frozenGreenBallCentre_holds
  have d9 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only (hI2 := hI2)
  have d10 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d11 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d12 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d13 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d14 := HarmonicBalls.clusterStrongCompatibilityStmt_of_volumeGrowth (hI2 := hI2)
  have d15 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d16 := MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence (hE := d5)
  have d17 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d18 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d19 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hEx) (h56 := d17)
  have d20 := MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint (hI2 := hI2) (h82 := h82)
  closed_5_1_lp_noSup (𝒮 := 𝒮) (ν := ν) (hC := hC) (h27 := d18) (hmodel := d16) (hFL := d1) (hstd := d3) (hGBC := d8)
    (hconf := hconf) (hK := d4) (hE := d5) (hE1 := d7) (hE2 := d2) (hscale := hscale) (hND := d6) (hcanon := hcanon)
    (h32 := d13) (h611 := d9) (h82 := h82) (hI2 := hI2) (hSup := d15) (hCons := d11) (hMono := d12) (hCompat := d10)
    (hBdry := d20) (hEx := hEx) (hThm11 := d19) (hProp56 := d17) (hloc := hloc) (hSC := d14) (hBG := hBG)

end MatedCRT.FirstPassClosure

namespace MatedCRT

open MeasureTheory
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_5_3_clean` (MatedCRT/FirstPass/Closure/HLsRewire53.lean) with the inputs supplied which follow from its other inputs: `hND : LQGMeasureNonDyadicDilationPart` by `MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds`, `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`, `hF3 : FrozenDiskGreenNonnegCont` by `MatedCRT.frozenDiskGreenNonnegCont_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_5_3_clean_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hscale : QuantumConeScalingInput)
    (hfirst : FPFirstHitVisits 𝒮) :
    MeanValueInequalityStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d3 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d6 := MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds
  have d7 := MatedCRT.coneCircleLawUniqueStep_holds
  have d8 := MatedCRT.frozenDiskGreenNonnegCont_holds
  have d9 := MatedCRT.frozenGreenBallCentre_holds
  have d10 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d11 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d12 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d13 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d14 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d15 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d16 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d15)
  closed_5_3_clean (𝒮 := 𝒮) (ν := ν) (hC := hC) (hBG := hBG) (hND := d6) (hstd := d3) (hCentre := d9) (hOpen := d13)
    (hSup := d14) (hCons := d11) (hMono := d12) (hCompat := d10) (hBdry := hBdry) (hExist := hExist) (hThm11 := d16)
    (hProp56 := d15) (hconf := hconf) (hI2 := hI2) (hK := d4) (hloc := hloc) (hE := d5) (hFL := d1) (hE1 := d7)
    (hE2 := d2) (hF3 := d8) (hscale := hscale) (hfirst := hfirst)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_6_1_lp_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with the inputs supplied which follow from its other inputs: `h27 : VolumeGrowthStmt` by `MatedCRT.volumeGrowthStmt_of_berestyckiGwynne`, `hmodel : FPWholePlaneLQGModel` by `MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`, `hND : LQGMeasureNonDyadicDilationPart` by `MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `h611 : VeryGoodAnnulusHarnackTypeStmt.{0}` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hBdry : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `h0 : FPWholePlaneLQGExistence` by `MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `h2 : FPWholePlaneLQGCoordinateChange` by `MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`, `hV : FPWholePlaneUpperVolumeTail` by `MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_6_1_lp_noSup_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hconf : FrozenHBInitialConfinement)
    (hscale : QuantumConeScalingInput)
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
    (h82 : TypicalPointManyGoodScalesStmt.{0})
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    IDLAUpperBoundStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d3 := MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d6 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d7 := MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds
  have d8 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d9 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  have d10 := MatedCRT.coneCircleLawUniqueStep_holds
  have d11 := MatedCRT.frozenGreenBallCentre_holds
  have d12 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only (hI2 := hI2)
  have d13 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d14 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d15 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d16 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d17 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d18 := MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence (hE := d6)
  have d19 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d20 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d21 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d19)
  have d22 := MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint (hI2 := hI2) (h82 := h82)
  closed_6_1_lp_noSup (𝒮 := 𝒮) (ν := ν) (hC := hC) (h27 := d20) (hmodel := d18) (hFL := d1) (hstd := d4)
    (hCentre := d11) (hconf := hconf) (hK := d5) (hE := d6) (hE1 := d10) (hE2 := d2) (hscale := hscale) (hND := d7)
    (hcanon := hcanon) (hOpen := d16) (h611 := d12) (h82 := h82) (hI2 := hI2) (hSup := d17) (hCons := d14)
    (hMono := d15) (hCompat := d13) (hBdry := d22) (hExist := hExist) (hThm11 := d21) (hProp56 := d19) (hloc := hloc)
    (hBG := hBG) (h0 := d9) (h2 := d8) (hV := d3)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_6_4_lp` (MatedCRT/FirstPass/Closure/CleanSec456LP.lean) with the inputs supplied which follow from its other inputs: `h0 : FPWholePlaneLQGExistence` by `MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `h2 : FPWholePlaneLQGCoordinateChange` by `MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`, `hV : FPWholePlaneUpperVolumeTail` by `MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_6_4_lp_derivedInputs :
    FirstPass64.GoodAnnulusPrevalenceUniformStmt :=
  have d1 := MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds
  have d2 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d3 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  closed_6_4_lp (h0 := d3) (h2 := d2) (hV := d1)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_6_10_lp` (MatedCRT/FirstPass/Closure/CleanSec456LP.lean) with the inputs supplied which follow from its other inputs: `h0 : FPWholePlaneLQGExistence` by `MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `h2 : FPWholePlaneLQGCoordinateChange` by `MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`, `hV : FPWholePlaneUpperVolumeTail` by `MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_6_10_lp_derivedInputs
    (𝒮 : SpaceFillingSLEModel)
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    IterativeBoundStmt 𝒮 :=
  have d1 := MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds
  have d2 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d3 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  closed_6_10_lp (𝒮 := 𝒮) (ν := ν) (hC := hC) (hBG := hBG) (h0 := d3) (h2 := d2) (hV := d1)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_7_1_lp` (MatedCRT/FirstPass/Closure/Clean61And71LP.lean) with the inputs supplied which follow from its other inputs: `h0 : FPWholePlaneLQGExistence` by `MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `h2 : FPWholePlaneLQGCoordinateChange` by `MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`, `hV : FPWholePlaneUpperVolumeTail` by `MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds`, `hND : LQGMeasureNonDyadicDilationPart` by `MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds`, `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56HB : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_7_1_lp_derivedInputs
    (𝒮 : SpaceFillingSLEModel)
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hscale : QuantumConeScalingInput)
    (hBdryHB : ClusterBoundaryMeasureZeroStmt.{0})
    (hExistHB : ExistenceHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0})
    (hlocHB : HarmonicBallLocalSetStmt.{0})
    (hrescale : ConeRescaledMeasureIsConeFieldInput) :
    DivSandpileUpperBoundStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d3 := MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d6 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d7 := MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds
  have d8 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d9 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  have d10 := MatedCRT.coneCircleLawUniqueStep_holds
  have d11 := MatedCRT.frozenGreenBallCentre_holds
  have d12 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2HB)
  have d13 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2HB)
  have d14 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2HB)
  have d15 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2HB)
  have d16 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2HB)
  have d17 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2HB)
  have d18 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExistHB) (h56 := d17)
  closed_7_1_lp (𝒮 := 𝒮) (ν := ν) (hC := hC) (hBG := hBG) (h0 := d9) (h2 := d8) (hV := d3) (hscale := hscale)
    (hND := d7) (hstd := d4) (hGBC := d11) (h32 := d15) (hSup := d16) (hCons := d13) (hMono := d14) (hCompat := d12)
    (hBdryHB := hBdryHB) (hExistHB := hExistHB) (hThm11 := d18) (hProp56HB := d17) (hconf := hconf) (hI2HB := hI2HB)
    (hK := d5) (hlocHB := hlocHB) (hE := d6) (hFL := d1) (hE1 := d10) (hE2 := d2) (hrescale := hrescale)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_8_1_lp_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with the inputs supplied which follow from its other inputs: `hm : MepsScalingInput 𝒮` by `MatedCRT.CertifiedReferenceModel.mepsScaling`, `h210 : DegreeMeasureConvergenceStmt 𝒮` by `MatedCRT.CertifiedReferenceModel.degreeMeasureConvergence`, `h34 : IntegralConvergenceGreenFunctionStmt 𝒮` by `MatedCRT.closed_3_4`, `h214 : GreenKernelUpperBoundStmt 𝒮` by `MatedCRT.CertifiedReferenceModel.greenKernelUpperBound`, `h28 : CellSizeEstimateStmt 𝒮` by `MatedCRT.CertifiedReferenceModel.cellSizeEstimate`, `h35c : DiscreteDirichletProblemCorrectedStmt 𝒮` by `MatedCRT.Phase2.closed_3_5_p2`, `h218 : ExitTimeUpperBoundStmt 𝒮` by `MatedCRT.CertifiedReferenceModel.exitTimeUpperBound`, `hH : FrozenDiscreteHolderContinuityCorrected 𝒮` by `MatedCRT.CertifiedReferenceModel.frozenDiscreteHolderContinuityCorrected`, `hcone : FrozenConeScalingLaw 𝒮` by `MatedCRT.CertifiedReferenceModel.frozenConeScaling`, `h23 : ConeHarmonicBallsStmt` by `MatedCRT.coneHarmonicBalls_of_numbered_results`, `h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt` by `MatedCRT.coneHarmonicBallsUpToFixedTimeCorrected_of_canonical`, `h33 : UniformConvergenceGreenKernelStmt 𝒮` by `MatedCRT.closed_3_3`, `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hBdry : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`, `hND : LQGMeasureNonDyadicDilationPart` by `MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds`, `h27 : VolumeGrowthStmt` by `MatedCRT.volumeGrowthStmt_of_berestyckiGwynne`, `hmodel : FPWholePlaneLQGModel` by `MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence`, `h611 : VeryGoodAnnulusHarnackTypeStmt.{0}` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only`, `h0 : FPWholePlaneLQGExistence` by `MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `h2 : FPWholePlaneLQGCoordinateChange` by `MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`, `hV : FPWholePlaneUpperVolumeTail` by `MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_8_1_lp_noSup_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hscale : QuantumConeScalingInput)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
    (h82 : TypicalPointManyGoodScalesStmt.{0}) :
    IDLAConstrainedConvergenceStmt 𝒮 :=
  have d1 := HarmonicBalls.firstPass_2_3
  have d2 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d3 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d4 := MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d6 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d7 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d8 := MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds
  have d9 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d10 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  have d11 := MatedCRT.HBRewire.FrozenGreenDiscPole_of_hb
  have d12 := MatedCRT.coneCircleAverageLocalityStep_proved
  have d13 := MatedCRT.coneCircleLawUniqueStep_holds
  have d14 := MatedCRT.frozenGreenBallCentre_holds
  have d15 := MatedCRT.frozenLQGTestIntegralMeasurable_holds
  have d16 := MatedCRT.frozenSuperharmonicMinimumPrinciple_holds
  have d17 := MatedCRT.frozenUniversalMeasurabilityOfAnalytic_holds
  have d18 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only (hI2 := hI2)
  have d19 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d20 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d21 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d22 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d23 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d24 := MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence (hE := d7)
  have d25 := MatedCRT.LQGMeasure.coneFieldScalingStep_proved_radial (hscale := hscale)
  have d26 := MatedCRT.LQGMeasure.lqgMeasureDilationCovariancePart_of_nonDyadic (hND := d8)
  have d27 := MatedCRT.coneScaleRadiusPosStep_of_input (hscale := hscale)
  have d28 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d29 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d30 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d28)
  have d31 := MatedCRT.LQGMeasure.coneLQGScalingStep_of_dilation (hIV := d26) (hpos := d27)
  have d32 := MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint (hI2 := hI2) (h82 := h82)
  have d33 := MatedCRT.CertifiedReferenceModel.cellSizeEstimate (h := hC)
  have d34 := MatedCRT.CertifiedReferenceModel.degreeMeasureConvergence (h := hC)
  have d35 := MatedCRT.CertifiedReferenceModel.exitTimeUpperBound (h := hC)
  have d36 := MatedCRT.CertifiedReferenceModel.frozenConeScaling (h := hC)
  have d37 := MatedCRT.CertifiedReferenceModel.frozenDiscreteHolderContinuityCorrected (h := hC)
  have d38 := MatedCRT.CertifiedReferenceModel.greenKernelUpperBound (h := hC)
  have d39 := MatedCRT.CertifiedReferenceModel.mepsScaling (h := hC)
  have d40 := MatedCRT.LQGMeasure.lqgMeasureNonAtomicPart_of_scaling (h27 := d29) (hfield := d25) (hlqg := d31)
  have d41 := MatedCRT.LQGMeasure.lqgMeasureProperties_of_citedInputs (hNA := d40) (hCL := d12) (hND := d8)
  have d42 := MatedCRT.Phase2.closed_3_5_p2 (ν := ν) (hC := hC) (h27 := d29)
  have d43 := MatedCRT.closed_3_3 (ν := ν) (hC := hC) (h27 := d29)
  have d44 := MatedCRT.closed_3_4 (ν := ν) (hC := hC) (h27 := d29)
  have d45 := MatedCRT.FirstPassClosure.coneHalfBallClosureInsideStep_proof (hI2 := hI2) (hK := d6) (hloc := hloc)
    (hEx := hExist) (hE := d7) (hFL := d2) (hBG := hBG)
  have d46 := MatedCRT.sourceHalfBallPathwiseStep_of_draft (hOpen := d22) (hSup := d23) (hCons := d20) (hMono := d21)
    (hCompat := d19) (hBdry := d32) (hExist := hExist) (hThm11 := d30) (hProp56 := d28) (hconf := hconf)
  have d47 := MatedCRT.coneHalfBallGood_of_source_sep (hU := d17) (hmeasT := d15) (hsrc := d46) (hstd := d5)
  have d48 := MatedCRT.coneCanonicalHalfBallStep_of_good (hgood := d47) (hmin := d16) (hC := d14) (hGB := d1)
    (hpole := d11)
  have d49 := MatedCRT.firstPass_2_4_canonical_of_inputs (hU := d17) (hmeasT := d15) (hsrc := d46) (hstd := d5)
    (hmin := d16) (hC := d14) (hGB := d1) (hpole := d11) (hcl := d45) (h27 := d29)
  have d50 := MatedCRT.coneHarmonicBallsUpToFixedTimeCorrected_of_canonical (h := d49)
  have d51 := MatedCRT.coneHarmonicBallsUpToFixedTimeStmt_of_canonical (hcan := d48) (hcl := d45)
  have d52 := MatedCRT.coneRescaledHalfBallHorizonUnique_fp (hcan := d48) (hcl := d45) (hrescale := hrescale)
  have d53 := MatedCRT.coneCanonicalFactor_proved (hcan := d48) (hcl := d45) (h27 := d29) (hE1 := d13) (hE2 := d3)
  have d54 := MatedCRT.firstPass_2_5_canonical_of_factor (hfac := d53) (hscale := hscale) (h22 := d41)
  have d55 := MatedCRT.coneScaleInvarianceUpToFixedTimeStmt_of_canonical (hcan := d48) (hcl := d45) (hc25 := d54)
    (hU := d52)
  have d56 := MatedCRT.coneHarmonicBalls_of_numbered_results (h24 := d51) (h25 := d55) (h27 := d29) (hscale := hscale)
    (h22 := d41)
  closed_8_1_lp_noSup (𝒮 := 𝒮) (ν := ν) (hC := hC) (hm := d39) (h210 := d34) (h34 := d44) (h214 := d38) (h28 := d33)
    (h35c := d42) (h218 := d35) (hH := d37) (hcone := d36) (h23 := d56) (h24c := d50) (h33 := d43) (hstd := d5)
    (hCentre := d14) (hOpen := d22) (hSup := d23) (hCons := d20) (hMono := d21) (hCompat := d19) (hBdry := d32)
    (hExist := hExist) (hThm11 := d30) (hProp56 := d28) (hconf := hconf) (hI2 := hI2) (hK := d6) (hloc := hloc)
    (hE := d7) (hFL := d2) (hBG := hBG) (hE1 := d13) (hE2 := d3) (hscale := hscale) (hND := d8) (hrescale := hrescale)
    (h27 := d29) (hmodel := d24) (hcanon := hcanon) (h611 := d18) (h82 := h82) (h0 := d10) (h2 := d9) (hV := d4)

end MatedCRT

namespace MatedCRT.FirstPass64


/-- The counted theorem `MatedCRT.FirstPass64.firstPass_6_5_uniform` (MatedCRT/FirstPass/S6q.lean) with the inputs supplied which follow from its other inputs: `h0 : FPWholePlaneLQGExistence` by `MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `h2 : FPWholePlaneLQGCoordinateChange` by `MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`, `hV : FPWholePlaneUpperVolumeTail` by `MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem firstPass_6_5_uniform_derivedInputs :
    AnnulusHitUniformStmt :=
  have d1 := MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds
  have d2 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d3 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  firstPass_6_5_uniform (h0 := d3) (h2 := d2) (hV := d1)

end MatedCRT.FirstPass64

namespace MatedCRT.LIClosed68Y

open MeasureTheory

/-- The counted theorem `MatedCRT.LIClosed68Y.firstPass_6_7` (MatedCRT/FirstPass/LIClosed68Y.lean) with the inputs supplied which follow from its other inputs: `hCC : S2VG.LitCoordChange` by `MatedCRT.FirstPass.Derived.litCoordChange_holds`, `hB1 : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem firstPass_6_7_derivedInputs
    {ν : ℝ → Measure SLEPathCode}
    {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence)
    (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    FaithfulConstantOrderLowerBoundStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.litCoordChange_holds
  firstPass_6_7 (ν := ν) (𝒮 := 𝒮) (hCRM := hCRM) (hLit := hLit) (hBM := hBM) (hCC := d2) (hB1 := d1) (hμ := hμ)
    (hBG := hBG)

end MatedCRT.LIClosed68Y

namespace MatedCRT.LIClosed68Y

open MeasureTheory

/-- The counted theorem `MatedCRT.LIClosed68Y.firstPass_6_8` (MatedCRT/FirstPass/LIClosed68Y.lean) with the inputs supplied which follow from its other inputs: `hCC : S2VG.LitCoordChange` by `MatedCRT.FirstPass.Derived.litCoordChange_holds`, `hB1 : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem firstPass_6_8_derivedInputs
    {ν : ℝ → Measure SLEPathCode}
    {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence)
    (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    FaithfulConstantOrderLowerBoundDivStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.litCoordChange_holds
  firstPass_6_8 (ν := ν) (𝒮 := 𝒮) (hCRM := hCRM) (hLit := hLit) (hBM := hBM) (hCC := d2) (hB1 := d1) (hμ := hμ)
    (hBG := hBG)

end MatedCRT.LIClosed68Y

namespace MatedCRT.LIClosed68Y

open MeasureTheory

/-- The counted theorem `MatedCRT.LIClosed68Y.firstPass_6_9` (MatedCRT/FirstPass/LIClosed68Y.lean) with the inputs supplied which follow from its other inputs: `hCC : S2VG.LitCoordChange` by `MatedCRT.FirstPass.Derived.litCoordChange_holds`, `hB1 : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem firstPass_6_9_derivedInputs
    {ν : ℝ → Measure SLEPathCode}
    {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence)
    (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    FaithfulChanceOfBeingAbsorbedStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.litCoordChange_holds
  firstPass_6_9 (ν := ν) (𝒮 := 𝒮) (hCRM := hCRM) (hLit := hLit) (hBM := hBM) (hCC := d2) (hB1 := d1) (hμ := hμ)
    (hBG := hBG)

end MatedCRT.LIClosed68Y
