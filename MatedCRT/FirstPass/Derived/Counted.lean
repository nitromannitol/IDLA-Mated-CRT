import HarmonicBalls.Assembly.ExistenceUniqueness
import HarmonicBalls.FirstPass.Closure
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
import MatedCRT.FirstPass.Closure.H35CorrectedRewire
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
import MatedCRT.FirstPass.Derived.ConeRescaledFieldHolds
import MatedCRT.FirstPass.Derived.ConeWholePlaneFieldLaw
import MatedCRT.FirstPass.Derived.CoordChangeZero
import MatedCRT.FirstPass.Derived.DiscGreenCentre
import MatedCRT.FirstPass.Derived.HBBallMassHolds
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
import MatedCRT.FirstPass.S3c
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

/-- The counted theorem `MatedCRT.closed_1_4_lp_noSC_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with the inputs supplied which follow from its other inputs: `hBG : FrozenBerestyckiGwynneConeBallMass` by `MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds`, `h0 : FPWholePlaneLQGExistence` by `MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `h2 : FPWholePlaneLQGCoordinateChange` by `MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`, `hV : FPWholePlaneUpperVolumeTail` by `MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds`, `hdiv : FrozenConeRadialDivergenceCorrected` by `MatedCRT.frozenConeRadialDivergenceCorrected_holds`, `hF3 : FrozenDiskGreenNonnegCont` by `MatedCRT.frozenDiskGreenNonnegCont_holds`, `h27 : VolumeGrowthStmt` by `MatedCRT.volumeGrowthStmt_of_berestyckiGwynne`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hconf : FrozenHBInitialConfinement` by `MatedCRT.FirstPass.Derived.frozenHBInitialConfinement_holds`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `h611 : FrozenVeryGoodAnnulusHarnackType` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only`, `h82 : FrozenTypicalPointManyGoodScales` by `MatedCRT.FirstPass.Derived.frozenTypicalPointManyGoodScales_holds`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hrescale : ConeRescaledMeasureIsConeFieldInput` by `MatedCRT.FirstPass.Derived.coneRescaledMeasureIsConeFieldInput_of_scaling`, `hND : LQGMeasureNonDyadicDilationPart` by `MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds`, `hBdryHB : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.FirstPass.Derived.frozenClusterBoundaryMeasureZero_holds`, `hExistHB : ExistenceHarmonicBallsStmt.{0}` by `MatedCRT.FirstPass.Derived.existenceHarmonicBallsStmt_holds`, `hProp56HB : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hI2HB : LQGVolumeGrowthAllScalesStmt.{0}` by `MatedCRT.FirstPass.Derived.frozenLQGVolumeGrowthAllScales_holds`, `hlocHB : HarmonicBallLocalSetStmt.{0}` by `MatedCRT.FirstPass.Derived.harmonicBallLocalSetStmt_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_1_4_lp_noSC_noSup_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮) :
    ConvergenceOfIDLAStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d3 := MatedCRT.FirstPass.Derived.existenceHarmonicBallsStmt_holds
  have d4 := MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  have d6 := MatedCRT.FirstPass.Derived.frozenClusterBoundaryMeasureZero_holds
  have d7 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d8 := MatedCRT.FirstPass.Derived.frozenHBInitialConfinement_holds
  have d9 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d10 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d11 := MatedCRT.FirstPass.Derived.frozenLQGVolumeGrowthAllScales_holds
  have d12 := MatedCRT.FirstPass.Derived.frozenTypicalPointManyGoodScales_holds
  have d13 := MatedCRT.FirstPass.Derived.harmonicBallLocalSetStmt_holds
  have d14 := MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds
  have d15 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d16 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  have d17 := MatedCRT.coneCircleLawUniqueStep_holds
  have d18 := MatedCRT.frozenConeRadialDivergenceCorrected_holds
  have d19 := MatedCRT.frozenDiskGreenNonnegCont_holds
  have d20 := MatedCRT.frozenGreenBallCentre_holds
  have d21 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only (hI2 := d11)
  have d22 := HarmonicBalls.clusterCompatibility_proved (hI2 := d11)
  have d23 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := d11)
  have d24 := HarmonicBalls.clusterMonotone_proved (hI2 := d11)
  have d25 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := d11)
  have d26 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := d11)
  have d27 := MatedCRT.FirstPass.Derived.coneRescaledMeasureIsConeFieldInput_of_scaling (hscale := hscale)
  have d28 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := d11)
  have d29 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := d5)
  have d30 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := d3) (h56 := d28)
  closed_1_4_lp_noSC_noSup (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hscale := hscale) (hEnvS := hEnvS) (hBG := d5)
    (h0 := d16) (h2 := d15) (hV := d4) (hdiv := d18) (hF3 := d19) (h27 := d29) (hFL := d1) (hstd := d7) (hGBC := d20)
    (hconf := d8) (hK := d9) (hE := d10) (hE1 := d17) (hE2 := d2) (hG15 := hG15) (h32 := d25) (h611 := d21)
    (h82 := d12) (hSup := d26) (hCons := d23) (hMono := d24) (hCompat := d22) (hThm11 := d30) (hrescale := d27)
    (hND := d14) (hBdryHB := d6) (hExistHB := d3) (hProp56HB := d28) (hI2HB := d11) (hlocHB := d13)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_1_6_lp_noSC_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with the inputs supplied which follow from its other inputs: `hBG : FrozenBerestyckiGwynneConeBallMass` by `MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds`, `h0 : FPWholePlaneLQGExistence` by `MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `h2 : FPWholePlaneLQGCoordinateChange` by `MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`, `hV : FPWholePlaneUpperVolumeTail` by `MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds`, `hdiv : FrozenConeRadialDivergenceCorrected` by `MatedCRT.frozenConeRadialDivergenceCorrected_holds`, `hF3 : FrozenDiskGreenNonnegCont` by `MatedCRT.frozenDiskGreenNonnegCont_holds`, `h27 : VolumeGrowthStmt` by `MatedCRT.volumeGrowthStmt_of_berestyckiGwynne`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hconf : FrozenHBInitialConfinement` by `MatedCRT.FirstPass.Derived.frozenHBInitialConfinement_holds`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `h611 : FrozenVeryGoodAnnulusHarnackType` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only`, `h82 : FrozenTypicalPointManyGoodScales` by `MatedCRT.FirstPass.Derived.frozenTypicalPointManyGoodScales_holds`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hrescale : ConeRescaledMeasureIsConeFieldInput` by `MatedCRT.FirstPass.Derived.coneRescaledMeasureIsConeFieldInput_of_scaling`, `hND : LQGMeasureNonDyadicDilationPart` by `MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds`, `hBdryHB : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.FirstPass.Derived.frozenClusterBoundaryMeasureZero_holds`, `hExistHB : ExistenceHarmonicBallsStmt.{0}` by `MatedCRT.FirstPass.Derived.existenceHarmonicBallsStmt_holds`, `hProp56HB : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hI2HB : LQGVolumeGrowthAllScalesStmt.{0}` by `MatedCRT.FirstPass.Derived.frozenLQGVolumeGrowthAllScales_holds`, `hlocHB : HarmonicBallLocalSetStmt.{0}` by `MatedCRT.FirstPass.Derived.harmonicBallLocalSetStmt_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_1_6_lp_noSC_noSup_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d3 := MatedCRT.FirstPass.Derived.existenceHarmonicBallsStmt_holds
  have d4 := MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  have d6 := MatedCRT.FirstPass.Derived.frozenClusterBoundaryMeasureZero_holds
  have d7 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d8 := MatedCRT.FirstPass.Derived.frozenHBInitialConfinement_holds
  have d9 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d10 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d11 := MatedCRT.FirstPass.Derived.frozenLQGVolumeGrowthAllScales_holds
  have d12 := MatedCRT.FirstPass.Derived.frozenTypicalPointManyGoodScales_holds
  have d13 := MatedCRT.FirstPass.Derived.harmonicBallLocalSetStmt_holds
  have d14 := MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds
  have d15 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d16 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  have d17 := MatedCRT.coneCircleLawUniqueStep_holds
  have d18 := MatedCRT.frozenConeRadialDivergenceCorrected_holds
  have d19 := MatedCRT.frozenDiskGreenNonnegCont_holds
  have d20 := MatedCRT.frozenGreenBallCentre_holds
  have d21 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only (hI2 := d11)
  have d22 := HarmonicBalls.clusterCompatibility_proved (hI2 := d11)
  have d23 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := d11)
  have d24 := HarmonicBalls.clusterMonotone_proved (hI2 := d11)
  have d25 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := d11)
  have d26 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := d11)
  have d27 := MatedCRT.FirstPass.Derived.coneRescaledMeasureIsConeFieldInput_of_scaling (hscale := hscale)
  have d28 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := d11)
  have d29 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := d5)
  have d30 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := d3) (h56 := d28)
  closed_1_6_lp_noSC_noSup (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hscale := hscale) (hEnvS := hEnvS) (hBG := d5)
    (h0 := d16) (h2 := d15) (hV := d4) (hdiv := d18) (hF3 := d19) (h27 := d29) (hFL := d1) (hstd := d7) (hGBC := d20)
    (hconf := d8) (hK := d9) (hE := d10) (hE1 := d17) (hE2 := d2) (hG15 := hG15) (h32 := d25) (h611 := d21)
    (h82 := d12) (hSup := d26) (hCons := d23) (hMono := d24) (hCompat := d22) (hThm11 := d30) (hrescale := d27)
    (hND := d14) (hBdryHB := d6) (hExistHB := d3) (hProp56HB := d28) (hI2HB := d11) (hlocHB := d13)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_2_3_lp` (MatedCRT/FirstPass/Closure/Clean2xLP.lean) with the inputs supplied which follow from its other inputs: `hBG : FrozenBerestyckiGwynneConeBallMass` by `MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds`, `hND : LQGMeasureNonDyadicDilationPart` by `MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds`, `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hBdryHB : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.FirstPass.Derived.frozenClusterBoundaryMeasureZero_holds`, `hExistHB : ExistenceHarmonicBallsStmt.{0}` by `MatedCRT.FirstPass.Derived.existenceHarmonicBallsStmt_holds`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56HB : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hconf : FrozenHBInitialConfinement` by `MatedCRT.FirstPass.Derived.frozenHBInitialConfinement_holds`, `hI2HB : LQGVolumeGrowthAllScalesStmt.{0}` by `MatedCRT.FirstPass.Derived.frozenLQGVolumeGrowthAllScales_holds`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hlocHB : HarmonicBallLocalSetStmt.{0}` by `MatedCRT.FirstPass.Derived.harmonicBallLocalSetStmt_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`, `hrescale : ConeRescaledMeasureIsConeFieldInput` by `MatedCRT.FirstPass.Derived.coneRescaledMeasureIsConeFieldInput_of_scaling`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_2_3_lp_derivedInputs
    (hscale : QuantumConeScalingInput) :
    ConeHarmonicBallsStmt :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d3 := MatedCRT.FirstPass.Derived.existenceHarmonicBallsStmt_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenClusterBoundaryMeasureZero_holds
  have d6 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d7 := MatedCRT.FirstPass.Derived.frozenHBInitialConfinement_holds
  have d8 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d9 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d10 := MatedCRT.FirstPass.Derived.frozenLQGVolumeGrowthAllScales_holds
  have d11 := MatedCRT.FirstPass.Derived.harmonicBallLocalSetStmt_holds
  have d12 := MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds
  have d13 := MatedCRT.coneCircleLawUniqueStep_holds
  have d14 := MatedCRT.frozenGreenBallCentre_holds
  have d15 := HarmonicBalls.clusterCompatibility_proved (hI2 := d10)
  have d16 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := d10)
  have d17 := HarmonicBalls.clusterMonotone_proved (hI2 := d10)
  have d18 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := d10)
  have d19 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := d10)
  have d20 := MatedCRT.FirstPass.Derived.coneRescaledMeasureIsConeFieldInput_of_scaling (hscale := hscale)
  have d21 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := d10)
  have d22 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := d3) (h56 := d21)
  closed_2_3_lp (hBG := d4) (hscale := hscale) (hND := d12) (hstd := d6) (hGBC := d14) (h32 := d18) (hSup := d19)
    (hCons := d16) (hMono := d17) (hCompat := d15) (hBdryHB := d5) (hExistHB := d3) (hThm11 := d22) (hProp56HB := d21)
    (hconf := d7) (hI2HB := d10) (hK := d8) (hlocHB := d11) (hE := d9) (hFL := d1) (hE1 := d13) (hE2 := d2)
    (hrescale := d20)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_2_4_lp` (MatedCRT/FirstPass/Closure/Clean2xLP.lean) with the inputs supplied which follow from its other inputs: `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hBdry : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.FirstPass.Derived.frozenClusterBoundaryMeasureZero_holds`, `hExist : ExistenceHarmonicBallsStmt.{0}` by `MatedCRT.FirstPass.Derived.existenceHarmonicBallsStmt_holds`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hconf : FrozenHBInitialConfinement` by `MatedCRT.FirstPass.Derived.frozenHBInitialConfinement_holds`, `hI2 : LQGVolumeGrowthAllScalesStmt.{0}` by `MatedCRT.FirstPass.Derived.frozenLQGVolumeGrowthAllScales_holds`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hloc : HarmonicBallLocalSetStmt.{0}` by `MatedCRT.FirstPass.Derived.harmonicBallLocalSetStmt_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hBG : FrozenBerestyckiGwynneConeBallMass` by `MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_2_4_lp_derivedInputs :
    ConeHarmonicBallsUpToFixedTimeCanonicalStmt :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.existenceHarmonicBallsStmt_holds
  have d3 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenClusterBoundaryMeasureZero_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d6 := MatedCRT.FirstPass.Derived.frozenHBInitialConfinement_holds
  have d7 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d8 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d9 := MatedCRT.FirstPass.Derived.frozenLQGVolumeGrowthAllScales_holds
  have d10 := MatedCRT.FirstPass.Derived.harmonicBallLocalSetStmt_holds
  have d11 := MatedCRT.frozenGreenBallCentre_holds
  have d12 := HarmonicBalls.clusterCompatibility_proved (hI2 := d9)
  have d13 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := d9)
  have d14 := HarmonicBalls.clusterMonotone_proved (hI2 := d9)
  have d15 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := d9)
  have d16 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := d9)
  have d17 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := d9)
  have d18 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := d2) (h56 := d17)
  closed_2_4_lp (hstd := d5) (hCentre := d11) (hOpen := d15) (hSup := d16) (hCons := d13) (hMono := d14)
    (hCompat := d12) (hBdry := d4) (hExist := d2) (hThm11 := d18) (hProp56 := d17) (hconf := d6) (hI2 := d9)
    (hK := d7) (hloc := d10) (hE := d8) (hFL := d1) (hBG := d3)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_2_5_lp` (MatedCRT/FirstPass/Closure/Clean2xLP.lean) with the inputs supplied which follow from its other inputs: `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hBdry : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.FirstPass.Derived.frozenClusterBoundaryMeasureZero_holds`, `hExist : ExistenceHarmonicBallsStmt.{0}` by `MatedCRT.FirstPass.Derived.existenceHarmonicBallsStmt_holds`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hconf : FrozenHBInitialConfinement` by `MatedCRT.FirstPass.Derived.frozenHBInitialConfinement_holds`, `hI2 : LQGVolumeGrowthAllScalesStmt.{0}` by `MatedCRT.FirstPass.Derived.frozenLQGVolumeGrowthAllScales_holds`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hloc : HarmonicBallLocalSetStmt.{0}` by `MatedCRT.FirstPass.Derived.harmonicBallLocalSetStmt_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hBG : FrozenBerestyckiGwynneConeBallMass` by `MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`, `hND : LQGMeasureNonDyadicDilationPart` by `MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_2_5_lp_derivedInputs
    (hscale : QuantumConeScalingInput) :
    ConeScaleInvarianceUpToFixedTimeCanonicalStmt :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d3 := MatedCRT.FirstPass.Derived.existenceHarmonicBallsStmt_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenClusterBoundaryMeasureZero_holds
  have d6 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d7 := MatedCRT.FirstPass.Derived.frozenHBInitialConfinement_holds
  have d8 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d9 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d10 := MatedCRT.FirstPass.Derived.frozenLQGVolumeGrowthAllScales_holds
  have d11 := MatedCRT.FirstPass.Derived.harmonicBallLocalSetStmt_holds
  have d12 := MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds
  have d13 := MatedCRT.coneCircleLawUniqueStep_holds
  have d14 := MatedCRT.frozenGreenBallCentre_holds
  have d15 := HarmonicBalls.clusterCompatibility_proved (hI2 := d10)
  have d16 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := d10)
  have d17 := HarmonicBalls.clusterMonotone_proved (hI2 := d10)
  have d18 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := d10)
  have d19 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := d10)
  have d20 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := d10)
  have d21 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := d3) (h56 := d20)
  closed_2_5_lp (hstd := d6) (hCentre := d14) (hOpen := d18) (hSup := d19) (hCons := d16) (hMono := d17)
    (hCompat := d15) (hBdry := d5) (hExist := d3) (hThm11 := d21) (hProp56 := d20) (hconf := d7) (hI2 := d10)
    (hK := d8) (hloc := d11) (hE := d9) (hFL := d1) (hBG := d4) (hE1 := d13) (hE2 := d2) (hscale := hscale)
    (hND := d12)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_2_6_lp` (MatedCRT/FirstPass/Closure/Clean2xLP.lean) with the inputs supplied which follow from its other inputs: `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hBdry : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.FirstPass.Derived.frozenClusterBoundaryMeasureZero_holds`, `hExist : ExistenceHarmonicBallsStmt.{0}` by `MatedCRT.FirstPass.Derived.existenceHarmonicBallsStmt_holds`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hconf : FrozenHBInitialConfinement` by `MatedCRT.FirstPass.Derived.frozenHBInitialConfinement_holds`, `hI2 : LQGVolumeGrowthAllScalesStmt.{0}` by `MatedCRT.FirstPass.Derived.frozenLQGVolumeGrowthAllScales_holds`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hloc : HarmonicBallLocalSetStmt.{0}` by `MatedCRT.FirstPass.Derived.harmonicBallLocalSetStmt_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hBG : FrozenBerestyckiGwynneConeBallMass` by `MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`, `hND : LQGMeasureNonDyadicDilationPart` by `MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_2_6_lp_derivedInputs
    (hscale : QuantumConeScalingInput) :
    ConeScaleInvarianceStmt :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d3 := MatedCRT.FirstPass.Derived.existenceHarmonicBallsStmt_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenClusterBoundaryMeasureZero_holds
  have d6 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d7 := MatedCRT.FirstPass.Derived.frozenHBInitialConfinement_holds
  have d8 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d9 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d10 := MatedCRT.FirstPass.Derived.frozenLQGVolumeGrowthAllScales_holds
  have d11 := MatedCRT.FirstPass.Derived.harmonicBallLocalSetStmt_holds
  have d12 := MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds
  have d13 := MatedCRT.coneCircleLawUniqueStep_holds
  have d14 := MatedCRT.frozenGreenBallCentre_holds
  have d15 := HarmonicBalls.clusterCompatibility_proved (hI2 := d10)
  have d16 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := d10)
  have d17 := HarmonicBalls.clusterMonotone_proved (hI2 := d10)
  have d18 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := d10)
  have d19 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := d10)
  have d20 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := d10)
  have d21 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := d3) (h56 := d20)
  closed_2_6_lp (hstd := d6) (hCentre := d14) (hOpen := d18) (hSup := d19) (hCons := d16) (hMono := d17)
    (hCompat := d15) (hBdry := d5) (hExist := d3) (hThm11 := d21) (hProp56 := d20) (hconf := d7) (hI2 := d10)
    (hK := d8) (hloc := d11) (hE := d9) (hFL := d1) (hBG := d4) (hE1 := d13) (hE2 := d2) (hscale := hscale)
    (hND := d12)

end MatedCRT

namespace MatedCRT

open MeasureTheory
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_2_19_ownBinders` (MatedCRT/FirstPass/Closure/OwnBinderRewire.lean) with the inputs supplied which follow from its other inputs: `hBG : FrozenBerestyckiGwynneConeBallMass` by `MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_2_19_ownBinders_derivedInputs
    (𝒮 : SpaceFillingSLEModel)
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) :
    ExpectedExitTimeExplicitBoundStmt 𝒮 :=
  have d1 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  closed_2_19_ownBinders (𝒮 := 𝒮) (ν := ν) (hC := hC) (hBG := d1)

end MatedCRT

namespace MatedCRT

open MeasureTheory
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_3_3_ownBinders` (MatedCRT/FirstPass/Closure/OwnBinderRewire.lean) with the inputs supplied which follow from its other inputs: `hBG : FrozenBerestyckiGwynneConeBallMass` by `MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_3_3_ownBinders_derivedInputs
    (𝒮 : SpaceFillingSLEModel)
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) :
    UniformConvergenceGreenKernelStmt 𝒮 :=
  have d1 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  closed_3_3_ownBinders (𝒮 := 𝒮) (ν := ν) (hC := hC) (hBG := d1)

end MatedCRT

namespace MatedCRT

open MeasureTheory
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_3_4_ownBinders` (MatedCRT/FirstPass/Closure/OwnBinderRewire.lean) with the inputs supplied which follow from its other inputs: `hBG : FrozenBerestyckiGwynneConeBallMass` by `MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_3_4_ownBinders_derivedInputs
    (𝒮 : SpaceFillingSLEModel)
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) :
    IntegralConvergenceGreenFunctionStmt 𝒮 :=
  have d1 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  closed_3_4_ownBinders (𝒮 := 𝒮) (ν := ν) (hC := hC) (hBG := d1)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_3_5_lp` (MatedCRT/FirstPass/Closure/CleanSec23LP.lean) with the inputs supplied which follow from its other inputs: `hBG : FrozenBerestyckiGwynneConeBallMass` by `MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_3_5_lp_derivedInputs
    (𝒮 : SpaceFillingSLEModel)
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) :
    DiscreteDirichletProblemCorrectedStmt 𝒮 :=
  have d1 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  closed_3_5_lp (𝒮 := 𝒮) (ν := ν) (hC := hC) (hBG := d1)

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

/-- The counted theorem `MatedCRT.closed_3_7_lp` (MatedCRT/FirstPass/Closure/CleanSec23LP.lean) with the inputs supplied which follow from its other inputs: `hBG : FrozenBerestyckiGwynneConeBallMass` by `MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds`, `hm : MepsScalingInput 𝒮` by `MatedCRT.CertifiedReferenceModel.mepsScaling`, `h32 : FrozenDiscreteHolderContinuityCorrected 𝒮` by `MatedCRT.CertifiedReferenceModel.frozenDiscreteHolderContinuityCorrected`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_3_7_lp_derivedInputs
    (𝒮 : SpaceFillingSLEModel)
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) :
    ConvergenceNormalizedExitTimeStmt 𝒮 :=
  have d1 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  have d2 := MatedCRT.CertifiedReferenceModel.frozenDiscreteHolderContinuityCorrected (h := hC)
  have d3 := MatedCRT.CertifiedReferenceModel.mepsScaling (h := hC)
  closed_3_7_lp (𝒮 := 𝒮) (ν := ν) (hC := hC) (hBG := d1) (hm := d3) (h32 := d2)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_4_1_lp` (MatedCRT/FirstPass/Closure/CleanSec456LP.lean) with the inputs supplied which follow from its other inputs: `hBG : FrozenBerestyckiGwynneConeBallMass` by `MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_4_1_lp_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) :
    ConvergenceDivisibleStmt 𝒮 :=
  have d1 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  closed_4_1_lp (𝒮 := 𝒮) (ν := ν) (hC := hC) (hBG := d1)

end MatedCRT

namespace MatedCRT.FirstPassClosure

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.FirstPassClosure.closed_4_2_lp` (MatedCRT/FirstPass/Closure/Clean42And5LP.lean) with the inputs supplied which follow from its other inputs: `h23 : ConeHarmonicBallsStmt` by `MatedCRT.coneHarmonicBalls_of_numbered_results`, `h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt` by `MatedCRT.coneHarmonicBallsUpToFixedTimeCorrected_of_canonical`, `h33 : UniformConvergenceGreenKernelStmt 𝒮` by `MatedCRT.Audit.StatementsSec3Sec5M1.three_three_final_reduction`, `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hBdry : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.FirstPass.Derived.frozenClusterBoundaryMeasureZero_holds`, `hExist : ExistenceHarmonicBallsStmt.{0}` by `MatedCRT.FirstPass.Derived.existenceHarmonicBallsStmt_holds`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hconf : FrozenHBInitialConfinement` by `MatedCRT.FirstPass.Derived.frozenHBInitialConfinement_holds`, `hI2 : FrozenLQGVolumeGrowthAllScales` by `MatedCRT.FirstPass.Derived.frozenLQGVolumeGrowthAllScales_holds`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hloc : HarmonicBallLocalSetStmt.{0}` by `MatedCRT.FirstPass.Derived.harmonicBallLocalSetStmt_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hBG : FrozenBerestyckiGwynneConeBallMass` by `MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`, `hND : LQGMeasureNonDyadicDilationPart` by `MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds`, `hrescale : ConeRescaledMeasureIsConeFieldInput` by `MatedCRT.FirstPass.Derived.coneRescaledMeasureIsConeFieldInput_of_scaling`. Same conclusion; the remaining binders are copied unchanged. -/
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
    (hscale : QuantumConeScalingInput) :
    DivSandpileLowerBoundStmt 𝒮 :=
  have d1 := HarmonicBalls.Closure.closure_2_3
  have d2 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d3 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d4 := MatedCRT.FirstPass.Derived.existenceHarmonicBallsStmt_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  have d6 := MatedCRT.FirstPass.Derived.frozenClusterBoundaryMeasureZero_holds
  have d7 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d8 := MatedCRT.FirstPass.Derived.frozenHBInitialConfinement_holds
  have d9 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d10 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d11 := MatedCRT.FirstPass.Derived.frozenLQGVolumeGrowthAllScales_holds
  have d12 := MatedCRT.FirstPass.Derived.harmonicBallLocalSetStmt_holds
  have d13 := MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds
  have d14 := MatedCRT.HBRewire.FrozenGreenDiscPole_of_hb
  have d15 := MatedCRT.coneCircleAverageLocalityStep_proved
  have d16 := MatedCRT.coneCircleLawUniqueStep_holds
  have d17 := MatedCRT.frozenGreenBallCentre_holds
  have d18 := MatedCRT.frozenLQGTestIntegralMeasurable_holds
  have d19 := MatedCRT.frozenSuperharmonicMinimumPrinciple_holds
  have d20 := MatedCRT.frozenUniversalMeasurabilityOfAnalytic_holds
  have d21 := HarmonicBalls.clusterCompatibility_proved (hI2 := d11)
  have d22 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := d11)
  have d23 := HarmonicBalls.clusterMonotone_proved (hI2 := d11)
  have d24 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := d11)
  have d25 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := d11)
  have d26 := MatedCRT.FirstPass.Derived.coneRescaledMeasureIsConeFieldInput_of_scaling (hscale := hscale)
  have d27 := MatedCRT.LQGMeasure.coneFieldScalingStep_proved_radial (hscale := hscale)
  have d28 := MatedCRT.LQGMeasure.lqgMeasureDilationCovariancePart_of_nonDyadic (hND := d13)
  have d29 := MatedCRT.coneScaleRadiusPosStep_of_input (hscale := hscale)
  have d30 := MatedCRT.firstPass_2_17_ownBinders (hBG := d5)
  have d31 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := d11)
  have d32 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := d5)
  have d33 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := d4) (h56 := d31)
  have d34 := MatedCRT.LQGMeasure.coneLQGScalingStep_of_dilation (hIV := d28) (hpos := d29)
  have d35 := MatedCRT.LQGMeasure.lqgMeasureNonAtomicPart_of_scaling (h27 := d32) (hfield := d27) (hlqg := d34)
  have d36 := MatedCRT.LQGMeasure.lqgMeasureProperties_of_citedInputs (hNA := d35) (hCL := d15) (hND := d13)
  have d37 := MatedCRT.discretePotentialTightnessAeStep_of_inputs (hm := hm) (h217 := d30) (h218 := h218) (hH := hH)
  have d38 := MatedCRT.Audit.StatementsSec3Sec5M1.three_three_final_reduction (𝒮 := 𝒮) (h210 := h210) (h34 := h34)
    (h214 := h214) (h28 := h28) (hAe := d37)
  have d39 := MatedCRT.FirstPassClosure.coneHalfBallClosureInsideStep_proof (hI2 := d11) (hK := d9) (hloc := d12)
    (hEx := d4) (hE := d10) (hFL := d2) (hBG := d5)
  have d40 := MatedCRT.sourceHalfBallPathwiseStep_of_draft (hOpen := d24) (hSup := d25) (hCons := d22) (hMono := d23)
    (hCompat := d21) (hBdry := d6) (hExist := d4) (hThm11 := d33) (hProp56 := d31) (hconf := d8)
  have d41 := MatedCRT.coneHalfBallGood_of_source_sep (hU := d20) (hmeasT := d18) (hsrc := d40) (hstd := d7)
  have d42 := MatedCRT.coneCanonicalHalfBallStep_of_good (hgood := d41) (hmin := d19) (hC := d17) (hGB := d1)
    (hpole := d14)
  have d43 := MatedCRT.firstPass_2_4_canonical_of_inputs (hU := d20) (hmeasT := d18) (hsrc := d40) (hstd := d7)
    (hmin := d19) (hC := d17) (hGB := d1) (hpole := d14) (hcl := d39) (h27 := d32)
  have d44 := MatedCRT.coneHarmonicBallsUpToFixedTimeCorrected_of_canonical (h := d43)
  have d45 := MatedCRT.coneHarmonicBallsUpToFixedTimeStmt_of_canonical (hcan := d42) (hcl := d39)
  have d46 := MatedCRT.coneRescaledHalfBallHorizonUnique_fp (hcan := d42) (hcl := d39) (hrescale := d26)
  have d47 := MatedCRT.coneCanonicalFactor_proved (hcan := d42) (hcl := d39) (h27 := d32) (hE1 := d16) (hE2 := d3)
  have d48 := MatedCRT.firstPass_2_5_canonical_of_factor (hfac := d47) (hscale := hscale) (h22 := d36)
  have d49 := MatedCRT.coneScaleInvarianceUpToFixedTimeStmt_of_canonical (hcan := d42) (hcl := d39) (hc25 := d48)
    (hU := d46)
  have d50 := MatedCRT.coneHarmonicBalls_of_numbered_results (h24 := d45) (h25 := d49) (h27 := d32) (hscale := hscale)
    (h22 := d36)
  closed_4_2_lp (𝒮 := 𝒮) (hm := hm) (h210 := h210) (h34 := h34) (h214 := h214) (h28 := h28) (h35c := h35c)
    (h218 := h218) (hH := hH) (hcone := hcone) (h23 := d50) (h24c := d44) (h33 := d38) (hstd := d7) (hCentre := d17)
    (hOpen := d24) (hSup := d25) (hCons := d22) (hMono := d23) (hCompat := d21) (hBdry := d6) (hExist := d4)
    (hThm11 := d33) (hProp56 := d31) (hconf := d8) (hI2 := d11) (hK := d9) (hloc := d12) (hE := d10) (hFL := d2)
    (hBG := d5) (hE1 := d16) (hE2 := d3) (hscale := hscale) (hND := d13) (hrescale := d26)

end MatedCRT.FirstPassClosure

namespace MatedCRT

open MeasureTheory
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_4_7_ownBinders` (MatedCRT/FirstPass/Closure/OwnBinderRewire.lean) with the inputs supplied which follow from its other inputs: `hBG : FrozenBerestyckiGwynneConeBallMass` by `MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_4_7_ownBinders_derivedInputs
    (𝒮 : SpaceFillingSLEModel)
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) :
    EquiboundedStmt 𝒮 :=
  have d1 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  closed_4_7_ownBinders (𝒮 := 𝒮) (ν := ν) (hC := hC) (hBG := d1)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_4_8_lp` (MatedCRT/FirstPass/Closure/CleanSec456LP.lean) with the inputs supplied which follow from its other inputs: `hBG : FrozenBerestyckiGwynneConeBallMass` by `MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_4_8_lp_derivedInputs
    (𝒮 : SpaceFillingSLEModel)
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) :
    SubsequentialPropertiesCorrectedStmt 𝒮 :=
  have d1 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  closed_4_8_lp (𝒮 := 𝒮) (ν := ν) (hC := hC) (hBG := d1)

end MatedCRT

namespace MatedCRT.FirstPassClosure

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.FirstPassClosure.closed_5_1_lp_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with the inputs supplied which follow from its other inputs: `h27 : VolumeGrowthStmt` by `MatedCRT.volumeGrowthStmt_of_berestyckiGwynne`, `hmodel : FPWholePlaneLQGModel` by `MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hconf : FrozenHBInitialConfinement` by `MatedCRT.FirstPass.Derived.frozenHBInitialConfinement_holds`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`, `hND : LQGMeasureNonDyadicDilationPart` by `MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `h611 : VeryGoodAnnulusHarnackTypeStmt.{0}` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only`, `h82 : TypicalPointManyGoodScalesStmt.{0}` by `MatedCRT.FirstPass.Derived.frozenTypicalPointManyGoodScales_holds`, `hI2 : LQGVolumeGrowthAllScalesStmt.{0}` by `MatedCRT.FirstPass.Derived.frozenLQGVolumeGrowthAllScales_holds`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hBdry : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.FirstPass.Derived.frozenClusterBoundaryMeasureZero_holds`, `hEx : ExistenceHarmonicBallsStmt.{0}` by `MatedCRT.FirstPass.Derived.existenceHarmonicBallsStmt_holds`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hloc : HarmonicBallLocalSetStmt.{0}` by `MatedCRT.FirstPass.Derived.harmonicBallLocalSetStmt_holds`, `hSC : ClusterStrongCompatibilityStmt.{0}` by `HarmonicBalls.clusterStrongCompatibilityStmt_of_volumeGrowth`, `hBG : FrozenBerestyckiGwynneConeBallMass` by `MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_5_1_lp_noSup_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮) :
    IDLALowerBoundStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d3 := MatedCRT.FirstPass.Derived.existenceHarmonicBallsStmt_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenClusterBoundaryMeasureZero_holds
  have d6 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d7 := MatedCRT.FirstPass.Derived.frozenHBInitialConfinement_holds
  have d8 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d9 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d10 := MatedCRT.FirstPass.Derived.frozenLQGVolumeGrowthAllScales_holds
  have d11 := MatedCRT.FirstPass.Derived.frozenTypicalPointManyGoodScales_holds
  have d12 := MatedCRT.FirstPass.Derived.harmonicBallLocalSetStmt_holds
  have d13 := MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds
  have d14 := MatedCRT.coneCircleLawUniqueStep_holds
  have d15 := MatedCRT.frozenGreenBallCentre_holds
  have d16 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only (hI2 := d10)
  have d17 := HarmonicBalls.clusterCompatibility_proved (hI2 := d10)
  have d18 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := d10)
  have d19 := HarmonicBalls.clusterMonotone_proved (hI2 := d10)
  have d20 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := d10)
  have d21 := HarmonicBalls.clusterStrongCompatibilityStmt_of_volumeGrowth (hI2 := d10)
  have d22 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := d10)
  have d23 := MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence (hE := d9)
  have d24 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := d10)
  have d25 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := d4)
  have d26 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := d3) (h56 := d24)
  closed_5_1_lp_noSup (𝒮 := 𝒮) (ν := ν) (hC := hC) (h27 := d25) (hmodel := d23) (hFL := d1) (hstd := d6) (hGBC := d15)
    (hconf := d7) (hK := d8) (hE := d9) (hE1 := d14) (hE2 := d2) (hscale := hscale) (hND := d13) (hcanon := hcanon)
    (h32 := d20) (h611 := d16) (h82 := d11) (hI2 := d10) (hSup := d22) (hCons := d18) (hMono := d19) (hCompat := d17)
    (hBdry := d5) (hEx := d3) (hThm11 := d26) (hProp56 := d24) (hloc := d12) (hSC := d21) (hBG := d4)

end MatedCRT.FirstPassClosure

namespace MatedCRT

open MeasureTheory
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_5_2_ownBinders` (MatedCRT/FirstPass/Closure/OwnBinderRewire.lean) with the inputs supplied which follow from its other inputs: `hBG : FrozenBerestyckiGwynneConeBallMass` by `MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_5_2_ownBinders_derivedInputs
    (𝒮 : SpaceFillingSLEModel)
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) :
    GeneralIDLALowerBoundStmt 𝒮 :=
  have d1 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  closed_5_2_ownBinders (𝒮 := 𝒮) (ν := ν) (hC := hC) (hBG := d1)

end MatedCRT

namespace MatedCRT

open MeasureTheory
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_5_3_clean` (MatedCRT/FirstPass/Closure/HLsRewire53.lean) with the inputs supplied which follow from its other inputs: `hBG : FrozenBerestyckiGwynneConeBallMass` by `MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds`, `hND : LQGMeasureNonDyadicDilationPart` by `MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds`, `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hBdry : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.FirstPass.Derived.frozenClusterBoundaryMeasureZero_holds`, `hExist : ExistenceHarmonicBallsStmt.{0}` by `MatedCRT.FirstPass.Derived.existenceHarmonicBallsStmt_holds`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hconf : FrozenHBInitialConfinement` by `MatedCRT.FirstPass.Derived.frozenHBInitialConfinement_holds`, `hI2 : LQGVolumeGrowthAllScalesStmt.{0}` by `MatedCRT.FirstPass.Derived.frozenLQGVolumeGrowthAllScales_holds`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hloc : HarmonicBallLocalSetStmt.{0}` by `MatedCRT.FirstPass.Derived.harmonicBallLocalSetStmt_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`, `hF3 : FrozenDiskGreenNonnegCont` by `MatedCRT.frozenDiskGreenNonnegCont_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_5_3_clean_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hfirst : FPFirstHitVisits 𝒮) :
    MeanValueInequalityStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d3 := MatedCRT.FirstPass.Derived.existenceHarmonicBallsStmt_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenClusterBoundaryMeasureZero_holds
  have d6 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d7 := MatedCRT.FirstPass.Derived.frozenHBInitialConfinement_holds
  have d8 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d9 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d10 := MatedCRT.FirstPass.Derived.frozenLQGVolumeGrowthAllScales_holds
  have d11 := MatedCRT.FirstPass.Derived.harmonicBallLocalSetStmt_holds
  have d12 := MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds
  have d13 := MatedCRT.coneCircleLawUniqueStep_holds
  have d14 := MatedCRT.frozenDiskGreenNonnegCont_holds
  have d15 := MatedCRT.frozenGreenBallCentre_holds
  have d16 := HarmonicBalls.clusterCompatibility_proved (hI2 := d10)
  have d17 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := d10)
  have d18 := HarmonicBalls.clusterMonotone_proved (hI2 := d10)
  have d19 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := d10)
  have d20 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := d10)
  have d21 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := d10)
  have d22 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := d3) (h56 := d21)
  closed_5_3_clean (𝒮 := 𝒮) (ν := ν) (hC := hC) (hBG := d4) (hND := d12) (hstd := d6) (hCentre := d15) (hOpen := d19)
    (hSup := d20) (hCons := d17) (hMono := d18) (hCompat := d16) (hBdry := d5) (hExist := d3) (hThm11 := d22)
    (hProp56 := d21) (hconf := d7) (hI2 := d10) (hK := d8) (hloc := d11) (hE := d9) (hFL := d1) (hE1 := d13)
    (hE2 := d2) (hF3 := d14) (hscale := hscale) (hfirst := hfirst)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_6_1_lp_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with the inputs supplied which follow from its other inputs: `h27 : VolumeGrowthStmt` by `MatedCRT.volumeGrowthStmt_of_berestyckiGwynne`, `hmodel : FPWholePlaneLQGModel` by `MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hconf : FrozenHBInitialConfinement` by `MatedCRT.FirstPass.Derived.frozenHBInitialConfinement_holds`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`, `hND : LQGMeasureNonDyadicDilationPart` by `MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `h611 : VeryGoodAnnulusHarnackTypeStmt.{0}` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only`, `h82 : TypicalPointManyGoodScalesStmt.{0}` by `MatedCRT.FirstPass.Derived.frozenTypicalPointManyGoodScales_holds`, `hI2 : FrozenLQGVolumeGrowthAllScales` by `MatedCRT.FirstPass.Derived.frozenLQGVolumeGrowthAllScales_holds`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hBdry : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.FirstPass.Derived.frozenClusterBoundaryMeasureZero_holds`, `hExist : ExistenceHarmonicBallsStmt.{0}` by `MatedCRT.FirstPass.Derived.existenceHarmonicBallsStmt_holds`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hloc : HarmonicBallLocalSetStmt.{0}` by `MatedCRT.FirstPass.Derived.harmonicBallLocalSetStmt_holds`, `hBG : FrozenBerestyckiGwynneConeBallMass` by `MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds`, `h0 : FPWholePlaneLQGExistence` by `MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `h2 : FPWholePlaneLQGCoordinateChange` by `MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`, `hV : FPWholePlaneUpperVolumeTail` by `MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_6_1_lp_noSup_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮) :
    IDLAUpperBoundStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d3 := MatedCRT.FirstPass.Derived.existenceHarmonicBallsStmt_holds
  have d4 := MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  have d6 := MatedCRT.FirstPass.Derived.frozenClusterBoundaryMeasureZero_holds
  have d7 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d8 := MatedCRT.FirstPass.Derived.frozenHBInitialConfinement_holds
  have d9 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d10 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d11 := MatedCRT.FirstPass.Derived.frozenLQGVolumeGrowthAllScales_holds
  have d12 := MatedCRT.FirstPass.Derived.frozenTypicalPointManyGoodScales_holds
  have d13 := MatedCRT.FirstPass.Derived.harmonicBallLocalSetStmt_holds
  have d14 := MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds
  have d15 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d16 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  have d17 := MatedCRT.coneCircleLawUniqueStep_holds
  have d18 := MatedCRT.frozenGreenBallCentre_holds
  have d19 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only (hI2 := d11)
  have d20 := HarmonicBalls.clusterCompatibility_proved (hI2 := d11)
  have d21 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := d11)
  have d22 := HarmonicBalls.clusterMonotone_proved (hI2 := d11)
  have d23 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := d11)
  have d24 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := d11)
  have d25 := MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence (hE := d10)
  have d26 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := d11)
  have d27 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := d5)
  have d28 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := d3) (h56 := d26)
  closed_6_1_lp_noSup (𝒮 := 𝒮) (ν := ν) (hC := hC) (h27 := d27) (hmodel := d25) (hFL := d1) (hstd := d7)
    (hCentre := d18) (hconf := d8) (hK := d9) (hE := d10) (hE1 := d17) (hE2 := d2) (hscale := hscale) (hND := d14)
    (hcanon := hcanon) (hOpen := d23) (h611 := d19) (h82 := d12) (hI2 := d11) (hSup := d24) (hCons := d21)
    (hMono := d22) (hCompat := d20) (hBdry := d6) (hExist := d3) (hThm11 := d28) (hProp56 := d26) (hloc := d13)
    (hBG := d5) (h0 := d16) (h2 := d15) (hV := d4)

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

/-- The counted theorem `MatedCRT.closed_6_10_lp` (MatedCRT/FirstPass/Closure/CleanSec456LP.lean) with the inputs supplied which follow from its other inputs: `hBG : FrozenBerestyckiGwynneConeBallMass` by `MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds`, `h0 : FPWholePlaneLQGExistence` by `MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `h2 : FPWholePlaneLQGCoordinateChange` by `MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`, `hV : FPWholePlaneUpperVolumeTail` by `MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_6_10_lp_derivedInputs
    (𝒮 : SpaceFillingSLEModel)
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) :
    IterativeBoundStmt 𝒮 :=
  have d1 := MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds
  have d2 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  have d3 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d4 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  closed_6_10_lp (𝒮 := 𝒮) (ν := ν) (hC := hC) (hBG := d2) (h0 := d4) (h2 := d3) (hV := d1)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_7_1_lp` (MatedCRT/FirstPass/Closure/Clean61And71LP.lean) with the inputs supplied which follow from its other inputs: `hBG : FrozenBerestyckiGwynneConeBallMass` by `MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds`, `h0 : FPWholePlaneLQGExistence` by `MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `h2 : FPWholePlaneLQGCoordinateChange` by `MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`, `hV : FPWholePlaneUpperVolumeTail` by `MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds`, `hND : LQGMeasureNonDyadicDilationPart` by `MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds`, `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hBdryHB : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.FirstPass.Derived.frozenClusterBoundaryMeasureZero_holds`, `hExistHB : ExistenceHarmonicBallsStmt.{0}` by `MatedCRT.FirstPass.Derived.existenceHarmonicBallsStmt_holds`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56HB : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hconf : FrozenHBInitialConfinement` by `MatedCRT.FirstPass.Derived.frozenHBInitialConfinement_holds`, `hI2HB : LQGVolumeGrowthAllScalesStmt.{0}` by `MatedCRT.FirstPass.Derived.frozenLQGVolumeGrowthAllScales_holds`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hlocHB : HarmonicBallLocalSetStmt.{0}` by `MatedCRT.FirstPass.Derived.harmonicBallLocalSetStmt_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`, `hrescale : ConeRescaledMeasureIsConeFieldInput` by `MatedCRT.FirstPass.Derived.coneRescaledMeasureIsConeFieldInput_of_scaling`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_7_1_lp_derivedInputs
    (𝒮 : SpaceFillingSLEModel)
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hscale : QuantumConeScalingInput) :
    DivSandpileUpperBoundStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d3 := MatedCRT.FirstPass.Derived.existenceHarmonicBallsStmt_holds
  have d4 := MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  have d6 := MatedCRT.FirstPass.Derived.frozenClusterBoundaryMeasureZero_holds
  have d7 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d8 := MatedCRT.FirstPass.Derived.frozenHBInitialConfinement_holds
  have d9 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d10 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d11 := MatedCRT.FirstPass.Derived.frozenLQGVolumeGrowthAllScales_holds
  have d12 := MatedCRT.FirstPass.Derived.harmonicBallLocalSetStmt_holds
  have d13 := MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds
  have d14 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d15 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  have d16 := MatedCRT.coneCircleLawUniqueStep_holds
  have d17 := MatedCRT.frozenGreenBallCentre_holds
  have d18 := HarmonicBalls.clusterCompatibility_proved (hI2 := d11)
  have d19 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := d11)
  have d20 := HarmonicBalls.clusterMonotone_proved (hI2 := d11)
  have d21 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := d11)
  have d22 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := d11)
  have d23 := MatedCRT.FirstPass.Derived.coneRescaledMeasureIsConeFieldInput_of_scaling (hscale := hscale)
  have d24 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := d11)
  have d25 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := d3) (h56 := d24)
  closed_7_1_lp (𝒮 := 𝒮) (ν := ν) (hC := hC) (hBG := d5) (h0 := d15) (h2 := d14) (hV := d4) (hscale := hscale)
    (hND := d13) (hstd := d7) (hGBC := d17) (h32 := d21) (hSup := d22) (hCons := d19) (hMono := d20) (hCompat := d18)
    (hBdryHB := d6) (hExistHB := d3) (hThm11 := d25) (hProp56HB := d24) (hconf := d8) (hI2HB := d11) (hK := d9)
    (hlocHB := d12) (hE := d10) (hFL := d1) (hE1 := d16) (hE2 := d2) (hrescale := d23)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_8_1_lp_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with the inputs supplied which follow from its other inputs: `hm : MepsScalingInput 𝒮` by `MatedCRT.CertifiedReferenceModel.mepsScaling`, `h210 : DegreeMeasureConvergenceStmt 𝒮` by `MatedCRT.CertifiedReferenceModel.degreeMeasureConvergence`, `h34 : IntegralConvergenceGreenFunctionStmt 𝒮` by `MatedCRT.closed_3_4`, `h214 : GreenKernelUpperBoundStmt 𝒮` by `MatedCRT.CertifiedReferenceModel.greenKernelUpperBound`, `h28 : CellSizeEstimateStmt 𝒮` by `MatedCRT.CertifiedReferenceModel.cellSizeEstimate`, `h35c : DiscreteDirichletProblemCorrectedStmt 𝒮` by `MatedCRT.Phase2.closed_3_5_p2`, `h218 : ExitTimeUpperBoundStmt 𝒮` by `MatedCRT.CertifiedReferenceModel.exitTimeUpperBound`, `hH : FrozenDiscreteHolderContinuityCorrected 𝒮` by `MatedCRT.CertifiedReferenceModel.frozenDiscreteHolderContinuityCorrected`, `hcone : FrozenConeScalingLaw 𝒮` by `MatedCRT.CertifiedReferenceModel.frozenConeScaling`, `h23 : ConeHarmonicBallsStmt` by `MatedCRT.coneHarmonicBalls_of_numbered_results`, `h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt` by `MatedCRT.coneHarmonicBallsUpToFixedTimeCorrected_of_canonical`, `h33 : UniformConvergenceGreenKernelStmt 𝒮` by `MatedCRT.closed_3_3`, `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hBdry : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.FirstPass.Derived.frozenClusterBoundaryMeasureZero_holds`, `hExist : ExistenceHarmonicBallsStmt.{0}` by `MatedCRT.FirstPass.Derived.existenceHarmonicBallsStmt_holds`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hconf : FrozenHBInitialConfinement` by `MatedCRT.FirstPass.Derived.frozenHBInitialConfinement_holds`, `hI2 : FrozenLQGVolumeGrowthAllScales` by `MatedCRT.FirstPass.Derived.frozenLQGVolumeGrowthAllScales_holds`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hloc : HarmonicBallLocalSetStmt.{0}` by `MatedCRT.FirstPass.Derived.harmonicBallLocalSetStmt_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hBG : FrozenBerestyckiGwynneConeBallMass` by `MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`, `hND : LQGMeasureNonDyadicDilationPart` by `MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds`, `hrescale : ConeRescaledMeasureIsConeFieldInput` by `MatedCRT.FirstPass.Derived.coneRescaledMeasureIsConeFieldInput_of_scaling`, `h27 : VolumeGrowthStmt` by `MatedCRT.volumeGrowthStmt_of_berestyckiGwynne`, `hmodel : FPWholePlaneLQGModel` by `MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence`, `h611 : VeryGoodAnnulusHarnackTypeStmt.{0}` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only`, `h82 : TypicalPointManyGoodScalesStmt.{0}` by `MatedCRT.FirstPass.Derived.frozenTypicalPointManyGoodScales_holds`, `h0 : FPWholePlaneLQGExistence` by `MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `h2 : FPWholePlaneLQGCoordinateChange` by `MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`, `hV : FPWholePlaneUpperVolumeTail` by `MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_8_1_lp_noSup_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮) :
    IDLAConstrainedConvergenceStmt 𝒮 :=
  have d1 := HarmonicBalls.Closure.closure_2_3
  have d2 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d3 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d4 := MatedCRT.FirstPass.Derived.existenceHarmonicBallsStmt_holds
  have d5 := MatedCRT.FirstPass.Derived.fpWholePlaneUpperVolumeTail_holds
  have d6 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  have d7 := MatedCRT.FirstPass.Derived.frozenClusterBoundaryMeasureZero_holds
  have d8 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d9 := MatedCRT.FirstPass.Derived.frozenHBInitialConfinement_holds
  have d10 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d11 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d12 := MatedCRT.FirstPass.Derived.frozenLQGVolumeGrowthAllScales_holds
  have d13 := MatedCRT.FirstPass.Derived.frozenTypicalPointManyGoodScales_holds
  have d14 := MatedCRT.FirstPass.Derived.harmonicBallLocalSetStmt_holds
  have d15 := MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds
  have d16 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d17 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  have d18 := MatedCRT.HBRewire.FrozenGreenDiscPole_of_hb
  have d19 := MatedCRT.coneCircleAverageLocalityStep_proved
  have d20 := MatedCRT.coneCircleLawUniqueStep_holds
  have d21 := MatedCRT.frozenGreenBallCentre_holds
  have d22 := MatedCRT.frozenLQGTestIntegralMeasurable_holds
  have d23 := MatedCRT.frozenSuperharmonicMinimumPrinciple_holds
  have d24 := MatedCRT.frozenUniversalMeasurabilityOfAnalytic_holds
  have d25 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only (hI2 := d12)
  have d26 := HarmonicBalls.clusterCompatibility_proved (hI2 := d12)
  have d27 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := d12)
  have d28 := HarmonicBalls.clusterMonotone_proved (hI2 := d12)
  have d29 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := d12)
  have d30 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := d12)
  have d31 := MatedCRT.FirstPass.Derived.coneRescaledMeasureIsConeFieldInput_of_scaling (hscale := hscale)
  have d32 := MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence (hE := d11)
  have d33 := MatedCRT.LQGMeasure.coneFieldScalingStep_proved_radial (hscale := hscale)
  have d34 := MatedCRT.LQGMeasure.lqgMeasureDilationCovariancePart_of_nonDyadic (hND := d15)
  have d35 := MatedCRT.coneScaleRadiusPosStep_of_input (hscale := hscale)
  have d36 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := d12)
  have d37 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := d6)
  have d38 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := d4) (h56 := d36)
  have d39 := MatedCRT.LQGMeasure.coneLQGScalingStep_of_dilation (hIV := d34) (hpos := d35)
  have d40 := MatedCRT.CertifiedReferenceModel.cellSizeEstimate (h := hC)
  have d41 := MatedCRT.CertifiedReferenceModel.degreeMeasureConvergence (h := hC)
  have d42 := MatedCRT.CertifiedReferenceModel.exitTimeUpperBound (h := hC)
  have d43 := MatedCRT.CertifiedReferenceModel.frozenConeScaling (h := hC)
  have d44 := MatedCRT.CertifiedReferenceModel.frozenDiscreteHolderContinuityCorrected (h := hC)
  have d45 := MatedCRT.CertifiedReferenceModel.greenKernelUpperBound (h := hC)
  have d46 := MatedCRT.CertifiedReferenceModel.mepsScaling (h := hC)
  have d47 := MatedCRT.LQGMeasure.lqgMeasureNonAtomicPart_of_scaling (h27 := d37) (hfield := d33) (hlqg := d39)
  have d48 := MatedCRT.LQGMeasure.lqgMeasureProperties_of_citedInputs (hNA := d47) (hCL := d19) (hND := d15)
  have d49 := MatedCRT.Phase2.closed_3_5_p2 (ν := ν) (hC := hC) (h27 := d37)
  have d50 := MatedCRT.closed_3_3 (ν := ν) (hC := hC) (h27 := d37)
  have d51 := MatedCRT.closed_3_4 (ν := ν) (hC := hC) (h27 := d37)
  have d52 := MatedCRT.FirstPassClosure.coneHalfBallClosureInsideStep_proof (hI2 := d12) (hK := d10) (hloc := d14)
    (hEx := d4) (hE := d11) (hFL := d2) (hBG := d6)
  have d53 := MatedCRT.sourceHalfBallPathwiseStep_of_draft (hOpen := d29) (hSup := d30) (hCons := d27) (hMono := d28)
    (hCompat := d26) (hBdry := d7) (hExist := d4) (hThm11 := d38) (hProp56 := d36) (hconf := d9)
  have d54 := MatedCRT.coneHalfBallGood_of_source_sep (hU := d24) (hmeasT := d22) (hsrc := d53) (hstd := d8)
  have d55 := MatedCRT.coneCanonicalHalfBallStep_of_good (hgood := d54) (hmin := d23) (hC := d21) (hGB := d1)
    (hpole := d18)
  have d56 := MatedCRT.firstPass_2_4_canonical_of_inputs (hU := d24) (hmeasT := d22) (hsrc := d53) (hstd := d8)
    (hmin := d23) (hC := d21) (hGB := d1) (hpole := d18) (hcl := d52) (h27 := d37)
  have d57 := MatedCRT.coneHarmonicBallsUpToFixedTimeCorrected_of_canonical (h := d56)
  have d58 := MatedCRT.coneHarmonicBallsUpToFixedTimeStmt_of_canonical (hcan := d55) (hcl := d52)
  have d59 := MatedCRT.coneRescaledHalfBallHorizonUnique_fp (hcan := d55) (hcl := d52) (hrescale := d31)
  have d60 := MatedCRT.coneCanonicalFactor_proved (hcan := d55) (hcl := d52) (h27 := d37) (hE1 := d20) (hE2 := d3)
  have d61 := MatedCRT.firstPass_2_5_canonical_of_factor (hfac := d60) (hscale := hscale) (h22 := d48)
  have d62 := MatedCRT.coneScaleInvarianceUpToFixedTimeStmt_of_canonical (hcan := d55) (hcl := d52) (hc25 := d61)
    (hU := d59)
  have d63 := MatedCRT.coneHarmonicBalls_of_numbered_results (h24 := d58) (h25 := d62) (h27 := d37) (hscale := hscale)
    (h22 := d48)
  closed_8_1_lp_noSup (𝒮 := 𝒮) (ν := ν) (hC := hC) (hm := d46) (h210 := d41) (h34 := d51) (h214 := d45) (h28 := d40)
    (h35c := d49) (h218 := d42) (hH := d44) (hcone := d43) (h23 := d63) (h24c := d57) (h33 := d50) (hstd := d8)
    (hCentre := d21) (hOpen := d29) (hSup := d30) (hCons := d27) (hMono := d28) (hCompat := d26) (hBdry := d7)
    (hExist := d4) (hThm11 := d38) (hProp56 := d36) (hconf := d9) (hI2 := d12) (hK := d10) (hloc := d14) (hE := d11)
    (hFL := d2) (hBG := d6) (hE1 := d20) (hE2 := d3) (hscale := hscale) (hND := d15) (hrescale := d31) (h27 := d37)
    (hmodel := d32) (hcanon := hcanon) (h611 := d25) (h82 := d13) (h0 := d17) (h2 := d16) (hV := d5)

end MatedCRT

namespace MatedCRT

open MeasureTheory
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.firstPass_2_17_ownBinders` (MatedCRT/FirstPass/Closure/OwnBinderRewire.lean) with the inputs supplied which follow from its other inputs: `hBG : FrozenBerestyckiGwynneConeBallMass` by `MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem firstPass_2_17_ownBinders_derivedInputs :
    BoundedExitTimeRVStmt :=
  have d1 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  firstPass_2_17_ownBinders (hBG := d1)

end MatedCRT

namespace MatedCRT.S3c

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- The counted theorem `MatedCRT.S3c.firstPass_3_1_faithful` (MatedCRT/FirstPass/S3c.lean) with the inputs supplied which follow from its other inputs: `h27 : VolumeGrowthStmt` by `MatedCRT.volumeGrowthStmt_of_berestyckiGwynne`. Same conclusion; the remaining binders are copied unchanged. -/
theorem firstPass_3_1_faithful_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) :
    DiscretePotentialTightnessPointwiseStmt 𝒮 :=
  have d1 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  have d2 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := d1)
  firstPass_3_1_faithful (𝒮 := 𝒮) (hm := hm) (h27 := d2) (h218 := h218) (h32 := h32)

end MatedCRT.S3c

namespace MatedCRT

open MeasureTheory Set

/-- The counted theorem `MatedCRT.firstPass_4_6_h35c` (MatedCRT/FirstPass/Closure/H35CorrectedRewire.lean) with the inputs supplied which follow from its other inputs: `h27 : VolumeGrowthStmt` by `MatedCRT.volumeGrowthStmt_of_berestyckiGwynne`. Same conclusion; the remaining binders are copied unchanged. -/
theorem firstPass_4_6_h35c_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮)
    (h35c : DiscreteDirichletProblemCorrectedStmt 𝒮)
    (h37 : ConvergenceNormalizedExitTimeStmt 𝒮) :
    SubsequentialConvergencePreparedStmt 𝒮 :=
  have d1 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  have d2 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := d1)
  firstPass_4_6_h35c (𝒮 := 𝒮) (hm := hm) (h27 := d2) (h218 := h218) (hH := hH) (h28 := h28) (h35c := h35c)
    (h37 := h37)

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

/-- The counted theorem `MatedCRT.LIClosed68Y.firstPass_6_7` (MatedCRT/FirstPass/LIClosed68Y.lean) with the inputs supplied which follow from its other inputs: `hCC : S2VG.LitCoordChange` by `MatedCRT.FirstPass.Derived.litCoordChange_holds`, `hB1 : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hBG : FrozenBerestyckiGwynneConeBallMass` by `MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem firstPass_6_7_derivedInputs
    {ν : ℝ → Measure SLEPathCode}
    {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence)
    (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence) :
    FaithfulConstantOrderLowerBoundStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  have d3 := MatedCRT.FirstPass.Derived.litCoordChange_holds
  firstPass_6_7 (ν := ν) (𝒮 := 𝒮) (hCRM := hCRM) (hLit := hLit) (hBM := hBM) (hCC := d3) (hB1 := d1) (hμ := hμ)
    (hBG := d2)

end MatedCRT.LIClosed68Y

namespace MatedCRT.LIClosed68Y

open MeasureTheory

/-- The counted theorem `MatedCRT.LIClosed68Y.firstPass_6_8` (MatedCRT/FirstPass/LIClosed68Y.lean) with the inputs supplied which follow from its other inputs: `hCC : S2VG.LitCoordChange` by `MatedCRT.FirstPass.Derived.litCoordChange_holds`, `hB1 : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hBG : FrozenBerestyckiGwynneConeBallMass` by `MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem firstPass_6_8_derivedInputs
    {ν : ℝ → Measure SLEPathCode}
    {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence)
    (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence) :
    FaithfulConstantOrderLowerBoundDivStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  have d3 := MatedCRT.FirstPass.Derived.litCoordChange_holds
  firstPass_6_8 (ν := ν) (𝒮 := 𝒮) (hCRM := hCRM) (hLit := hLit) (hBM := hBM) (hCC := d3) (hB1 := d1) (hμ := hμ)
    (hBG := d2)

end MatedCRT.LIClosed68Y

namespace MatedCRT.LIClosed68Y

open MeasureTheory

/-- The counted theorem `MatedCRT.LIClosed68Y.firstPass_6_9` (MatedCRT/FirstPass/LIClosed68Y.lean) with the inputs supplied which follow from its other inputs: `hCC : S2VG.LitCoordChange` by `MatedCRT.FirstPass.Derived.litCoordChange_holds`, `hB1 : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hBG : FrozenBerestyckiGwynneConeBallMass` by `MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem firstPass_6_9_derivedInputs
    {ν : ℝ → Measure SLEPathCode}
    {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence)
    (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence) :
    FaithfulChanceOfBeingAbsorbedStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  have d3 := MatedCRT.FirstPass.Derived.litCoordChange_holds
  firstPass_6_9 (ν := ν) (𝒮 := 𝒮) (hCRM := hCRM) (hLit := hLit) (hBM := hBM) (hCC := d3) (hB1 := d1) (hμ := hμ)
    (hBG := d2)

end MatedCRT.LIClosed68Y
