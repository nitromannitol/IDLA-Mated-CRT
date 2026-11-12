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
import MatedCRT.FirstPass.Derived.ConeRadialDivergence
import MatedCRT.FirstPass.Derived.ConeWholePlaneFieldLaw
import MatedCRT.FirstPass.Derived.DiscGreenCentre
import MatedCRT.FirstPass.Derived.HarmonicBallsVolumeGrowth
import MatedCRT.FirstPass.Derived.LQGMeasureInputs
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

/-- The counted theorem `MatedCRT.closed_1_4_lp_noSC_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with the inputs supplied which follow from its other inputs: `h0 : FPWholePlaneLQGExistence` by `MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `h2 : FPWholePlaneLQGCoordinateChange` by `MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`, `hdiv : FrozenConeRadialDivergenceCorrected` by `MatedCRT.frozenConeRadialDivergenceCorrected_holds`, `hF3 : FrozenDiskGreenNonnegCont` by `MatedCRT.frozenDiskGreenNonnegCont_holds`, `h27 : VolumeGrowthStmt` by `MatedCRT.volumeGrowthStmt_of_berestyckiGwynne`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `h611 : FrozenVeryGoodAnnulusHarnackType` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hBdryHB : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint`, `hProp56HB : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_1_4_lp_noSC_noSup_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hV : FPWholePlaneUpperVolumeTail)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE2 : ConeReferenceExistsStep)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hExistHB : ExistenceHarmonicBallsStmt.{0})
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0})
    (hlocHB : HarmonicBallLocalSetStmt.{0}) :
    ConvergenceOfIDLAStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d3 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d4 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  have d5 := MatedCRT.coneCircleLawUniqueStep_holds
  have d6 := MatedCRT.frozenConeRadialDivergenceCorrected_holds
  have d7 := MatedCRT.frozenDiskGreenNonnegCont_holds
  have d8 := MatedCRT.frozenGreenBallCentre_holds
  have d9 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only (hI2 := hI2HB)
  have d10 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2HB)
  have d11 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2HB)
  have d12 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2HB)
  have d13 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2HB)
  have d14 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2HB)
  have d15 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2HB)
  have d16 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d17 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExistHB) (h56 := d15)
  have d18 := MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint (hI2 := hI2HB) (h82 := h82)
  closed_1_4_lp_noSC_noSup (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hscale := hscale) (hEnvS := hEnvS) (hBG := hBG)
    (h0 := d4) (h2 := d3) (hV := hV) (hdiv := d6) (hF3 := d7) (h27 := d16) (hFL := d1) (hstd := hstd) (hGBC := d8)
    (hconf := hconf) (hK := hK) (hE := d2) (hE1 := d5) (hE2 := hE2) (hG15 := hG15) (h32 := d13) (h611 := d9)
    (h82 := h82) (hSup := d14) (hCons := d11) (hMono := d12) (hCompat := d10) (hThm11 := d17) (hrescale := hrescale)
    (hND := hND) (hBdryHB := d18) (hExistHB := hExistHB) (hProp56HB := d15) (hI2HB := hI2HB) (hlocHB := hlocHB)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_1_6_lp_noSC_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with the inputs supplied which follow from its other inputs: `h0 : FPWholePlaneLQGExistence` by `MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `h2 : FPWholePlaneLQGCoordinateChange` by `MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`, `hdiv : FrozenConeRadialDivergenceCorrected` by `MatedCRT.frozenConeRadialDivergenceCorrected_holds`, `hF3 : FrozenDiskGreenNonnegCont` by `MatedCRT.frozenDiskGreenNonnegCont_holds`, `h27 : VolumeGrowthStmt` by `MatedCRT.volumeGrowthStmt_of_berestyckiGwynne`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `h611 : FrozenVeryGoodAnnulusHarnackType` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hBdryHB : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint`, `hProp56HB : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_1_6_lp_noSC_noSup_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hV : FPWholePlaneUpperVolumeTail)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE2 : ConeReferenceExistsStep)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hExistHB : ExistenceHarmonicBallsStmt.{0})
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0})
    (hlocHB : HarmonicBallLocalSetStmt.{0}) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d3 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d4 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  have d5 := MatedCRT.coneCircleLawUniqueStep_holds
  have d6 := MatedCRT.frozenConeRadialDivergenceCorrected_holds
  have d7 := MatedCRT.frozenDiskGreenNonnegCont_holds
  have d8 := MatedCRT.frozenGreenBallCentre_holds
  have d9 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only (hI2 := hI2HB)
  have d10 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2HB)
  have d11 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2HB)
  have d12 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2HB)
  have d13 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2HB)
  have d14 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2HB)
  have d15 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2HB)
  have d16 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d17 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExistHB) (h56 := d15)
  have d18 := MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint (hI2 := hI2HB) (h82 := h82)
  closed_1_6_lp_noSC_noSup (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hscale := hscale) (hEnvS := hEnvS) (hBG := hBG)
    (h0 := d4) (h2 := d3) (hV := hV) (hdiv := d6) (hF3 := d7) (h27 := d16) (hFL := d1) (hstd := hstd) (hGBC := d8)
    (hconf := hconf) (hK := hK) (hE := d2) (hE1 := d5) (hE2 := hE2) (hG15 := hG15) (h32 := d13) (h611 := d9)
    (h82 := h82) (hSup := d14) (hCons := d11) (hMono := d12) (hCompat := d10) (hThm11 := d17) (hrescale := hrescale)
    (hND := hND) (hBdryHB := d18) (hExistHB := hExistHB) (hProp56HB := d15) (hI2HB := hI2HB) (hlocHB := hlocHB)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_2_3_lp` (MatedCRT/FirstPass/Closure/Clean2xLP.lean) with the inputs supplied which follow from its other inputs: `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56HB : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_2_3_lp_derivedInputs
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hscale : QuantumConeScalingInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hBdryHB : ClusterBoundaryMeasureZeroStmt.{0})
    (hExistHB : ExistenceHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hlocHB : HarmonicBallLocalSetStmt.{0})
    (hE2 : ConeReferenceExistsStep)
    (hrescale : ConeRescaledMeasureIsConeFieldInput) :
    ConeHarmonicBallsStmt :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d3 := MatedCRT.coneCircleLawUniqueStep_holds
  have d4 := MatedCRT.frozenGreenBallCentre_holds
  have d5 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2HB)
  have d6 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2HB)
  have d7 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2HB)
  have d8 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2HB)
  have d9 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2HB)
  have d10 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2HB)
  have d11 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExistHB) (h56 := d10)
  closed_2_3_lp (hBG := hBG) (hscale := hscale) (hND := hND) (hstd := hstd) (hGBC := d4) (h32 := d8) (hSup := d9)
    (hCons := d6) (hMono := d7) (hCompat := d5) (hBdryHB := hBdryHB) (hExistHB := hExistHB) (hThm11 := d11)
    (hProp56HB := d10) (hconf := hconf) (hI2HB := hI2HB) (hK := hK) (hlocHB := hlocHB) (hE := d2) (hFL := d1)
    (hE1 := d3) (hE2 := hE2) (hrescale := hrescale)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_2_4_lp` (MatedCRT/FirstPass/Closure/Clean2xLP.lean) with the inputs supplied which follow from its other inputs: `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_2_4_lp_derivedInputs
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    ConeHarmonicBallsUpToFixedTimeCanonicalStmt :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d3 := MatedCRT.frozenGreenBallCentre_holds
  have d4 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d5 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d6 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d7 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d8 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d9 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d10 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d9)
  closed_2_4_lp (hstd := hstd) (hCentre := d3) (hOpen := d7) (hSup := d8) (hCons := d5) (hMono := d6) (hCompat := d4)
    (hBdry := hBdry) (hExist := hExist) (hThm11 := d10) (hProp56 := d9) (hconf := hconf) (hI2 := hI2) (hK := hK)
    (hloc := hloc) (hE := d2) (hFL := d1) (hBG := hBG)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_2_5_lp` (MatedCRT/FirstPass/Closure/Clean2xLP.lean) with the inputs supplied which follow from its other inputs: `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_2_5_lp_derivedInputs
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput)
    (hND : LQGMeasureNonDyadicDilationPart) :
    ConeScaleInvarianceUpToFixedTimeCanonicalStmt :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d3 := MatedCRT.coneCircleLawUniqueStep_holds
  have d4 := MatedCRT.frozenGreenBallCentre_holds
  have d5 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d6 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d7 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d8 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d9 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d10 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d11 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d10)
  closed_2_5_lp (hstd := hstd) (hCentre := d4) (hOpen := d8) (hSup := d9) (hCons := d6) (hMono := d7) (hCompat := d5)
    (hBdry := hBdry) (hExist := hExist) (hThm11 := d11) (hProp56 := d10) (hconf := hconf) (hI2 := hI2) (hK := hK)
    (hloc := hloc) (hE := d2) (hFL := d1) (hBG := hBG) (hE1 := d3) (hE2 := hE2) (hscale := hscale) (hND := hND)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_2_6_lp` (MatedCRT/FirstPass/Closure/Clean2xLP.lean) with the inputs supplied which follow from its other inputs: `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_2_6_lp_derivedInputs
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput)
    (hND : LQGMeasureNonDyadicDilationPart) :
    ConeScaleInvarianceStmt :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d3 := MatedCRT.coneCircleLawUniqueStep_holds
  have d4 := MatedCRT.frozenGreenBallCentre_holds
  have d5 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d6 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d7 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d8 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d9 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d10 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d11 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d10)
  closed_2_6_lp (hstd := hstd) (hCentre := d4) (hOpen := d8) (hSup := d9) (hCons := d6) (hMono := d7) (hCompat := d5)
    (hBdry := hBdry) (hExist := hExist) (hThm11 := d11) (hProp56 := d10) (hconf := hconf) (hI2 := hI2) (hK := hK)
    (hloc := hloc) (hE := d2) (hFL := d1) (hBG := hBG) (hE1 := d3) (hE2 := hE2) (hscale := hscale) (hND := hND)

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

/-- The counted theorem `MatedCRT.FirstPassClosure.closed_4_2_lp` (MatedCRT/FirstPass/Closure/Clean42And5LP.lean) with the inputs supplied which follow from its other inputs: `h23 : ConeHarmonicBallsStmt` by `MatedCRT.coneHarmonicBalls_of_numbered_results`, `h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt` by `MatedCRT.coneHarmonicBallsUpToFixedTimeCorrected_of_canonical`, `h33 : UniformConvergenceGreenKernelStmt 𝒮` by `MatedCRT.Audit.StatementsSec3Sec5M1.three_three_final_reduction`, `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`. Same conclusion; the remaining binders are copied unchanged. -/
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
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hrescale : ConeRescaledMeasureIsConeFieldInput) :
    DivSandpileLowerBoundStmt 𝒮 :=
  have d1 := HarmonicBalls.firstPass_2_3
  have d2 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d3 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d4 := MatedCRT.HBRewire.FrozenGreenDiscPole_of_hb
  have d5 := MatedCRT.coneCircleAverageLocalityStep_proved
  have d6 := MatedCRT.coneCircleLawUniqueStep_holds
  have d7 := MatedCRT.frozenGreenBallCentre_holds
  have d8 := MatedCRT.frozenLQGTestIntegralMeasurable_holds
  have d9 := MatedCRT.frozenSuperharmonicMinimumPrinciple_holds
  have d10 := MatedCRT.frozenUniversalMeasurabilityOfAnalytic_holds
  have d11 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d12 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d13 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d14 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d15 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d16 := MatedCRT.LQGMeasure.coneFieldScalingStep_proved_radial (hscale := hscale)
  have d17 := MatedCRT.LQGMeasure.lqgMeasureDilationCovariancePart_of_nonDyadic (hND := hND)
  have d18 := MatedCRT.coneScaleRadiusPosStep_of_input (hscale := hscale)
  have d19 := MatedCRT.firstPass_2_17_ownBinders (hBG := hBG)
  have d20 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d21 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d22 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d20)
  have d23 := MatedCRT.LQGMeasure.coneLQGScalingStep_of_dilation (hIV := d17) (hpos := d18)
  have d24 := MatedCRT.LQGMeasure.lqgMeasureNonAtomicPart_of_scaling (h27 := d21) (hfield := d16) (hlqg := d23)
  have d25 := MatedCRT.LQGMeasure.lqgMeasureProperties_of_citedInputs (hNA := d24) (hCL := d5) (hND := hND)
  have d26 := MatedCRT.discretePotentialTightnessAeStep_of_inputs (hm := hm) (h217 := d19) (h218 := h218) (hH := hH)
  have d27 := MatedCRT.Audit.StatementsSec3Sec5M1.three_three_final_reduction (𝒮 := 𝒮) (h210 := h210) (h34 := h34)
    (h214 := h214) (h28 := h28) (hAe := d26)
  have d28 := MatedCRT.FirstPassClosure.coneHalfBallClosureInsideStep_proof (hI2 := hI2) (hK := hK) (hloc := hloc)
    (hEx := hExist) (hE := d3) (hFL := d2) (hBG := hBG)
  have d29 := MatedCRT.sourceHalfBallPathwiseStep_of_draft (hOpen := d14) (hSup := d15) (hCons := d12) (hMono := d13)
    (hCompat := d11) (hBdry := hBdry) (hExist := hExist) (hThm11 := d22) (hProp56 := d20) (hconf := hconf)
  have d30 := MatedCRT.coneHalfBallGood_of_source_sep (hU := d10) (hmeasT := d8) (hsrc := d29) (hstd := hstd)
  have d31 := MatedCRT.coneCanonicalHalfBallStep_of_good (hgood := d30) (hmin := d9) (hC := d7) (hGB := d1)
    (hpole := d4)
  have d32 := MatedCRT.firstPass_2_4_canonical_of_inputs (hU := d10) (hmeasT := d8) (hsrc := d29) (hstd := hstd)
    (hmin := d9) (hC := d7) (hGB := d1) (hpole := d4) (hcl := d28) (h27 := d21)
  have d33 := MatedCRT.coneHarmonicBallsUpToFixedTimeCorrected_of_canonical (h := d32)
  have d34 := MatedCRT.coneHarmonicBallsUpToFixedTimeStmt_of_canonical (hcan := d31) (hcl := d28)
  have d35 := MatedCRT.coneRescaledHalfBallHorizonUnique_fp (hcan := d31) (hcl := d28) (hrescale := hrescale)
  have d36 := MatedCRT.coneCanonicalFactor_proved (hcan := d31) (hcl := d28) (h27 := d21) (hE1 := d6) (hE2 := hE2)
  have d37 := MatedCRT.firstPass_2_5_canonical_of_factor (hfac := d36) (hscale := hscale) (h22 := d25)
  have d38 := MatedCRT.coneScaleInvarianceUpToFixedTimeStmt_of_canonical (hcan := d31) (hcl := d28) (hc25 := d37)
    (hU := d35)
  have d39 := MatedCRT.coneHarmonicBalls_of_numbered_results (h24 := d34) (h25 := d38) (h27 := d21) (hscale := hscale)
    (h22 := d25)
  closed_4_2_lp (𝒮 := 𝒮) (hm := hm) (h210 := h210) (h34 := h34) (h214 := h214) (h28 := h28) (h35c := h35c)
    (h218 := h218) (hH := hH) (hcone := hcone) (h23 := d39) (h24c := d33) (h33 := d27) (hstd := hstd) (hCentre := d7)
    (hOpen := d14) (hSup := d15) (hCons := d12) (hMono := d13) (hCompat := d11) (hBdry := hBdry) (hExist := hExist)
    (hThm11 := d22) (hProp56 := d20) (hconf := hconf) (hI2 := hI2) (hK := hK) (hloc := hloc) (hE := d3) (hFL := d2)
    (hBG := hBG) (hE1 := d6) (hE2 := hE2) (hscale := hscale) (hND := hND) (hrescale := hrescale)

end MatedCRT.FirstPassClosure

namespace MatedCRT.FirstPassClosure

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.FirstPassClosure.closed_5_1_lp_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with the inputs supplied which follow from its other inputs: `h27 : VolumeGrowthStmt` by `MatedCRT.volumeGrowthStmt_of_berestyckiGwynne`, `hmodel : FPWholePlaneLQGModel` by `MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `h611 : VeryGoodAnnulusHarnackTypeStmt.{0}` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hBdry : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hSC : ClusterStrongCompatibilityStmt.{0}` by `HarmonicBalls.clusterStrongCompatibilityStmt_of_volumeGrowth`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_5_1_lp_noSup_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
    (h82 : TypicalPointManyGoodScalesStmt.{0})
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hEx : ExistenceHarmonicBallsStmt.{0})
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    IDLALowerBoundStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d3 := MatedCRT.coneCircleLawUniqueStep_holds
  have d4 := MatedCRT.frozenGreenBallCentre_holds
  have d5 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only (hI2 := hI2)
  have d6 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d7 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d8 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d9 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d10 := HarmonicBalls.clusterStrongCompatibilityStmt_of_volumeGrowth (hI2 := hI2)
  have d11 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d12 := MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence (hE := d2)
  have d13 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d14 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d15 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hEx) (h56 := d13)
  have d16 := MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint (hI2 := hI2) (h82 := h82)
  closed_5_1_lp_noSup (𝒮 := 𝒮) (ν := ν) (hC := hC) (h27 := d14) (hmodel := d12) (hFL := d1) (hstd := hstd)
    (hGBC := d4) (hconf := hconf) (hK := hK) (hE := d2) (hE1 := d3) (hE2 := hE2) (hscale := hscale) (hND := hND)
    (hcanon := hcanon) (h32 := d9) (h611 := d5) (h82 := h82) (hI2 := hI2) (hSup := d11) (hCons := d7) (hMono := d8)
    (hCompat := d6) (hBdry := d16) (hEx := hEx) (hThm11 := d15) (hProp56 := d13) (hloc := hloc) (hSC := d10)
    (hBG := hBG)

end MatedCRT.FirstPassClosure

namespace MatedCRT

open MeasureTheory
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_5_3_clean` (MatedCRT/FirstPass/Closure/HLsRewire53.lean) with the inputs supplied which follow from its other inputs: `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hF3 : FrozenDiskGreenNonnegCont` by `MatedCRT.frozenDiskGreenNonnegCont_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_5_3_clean_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput)
    (hfirst : FPFirstHitVisits 𝒮) :
    MeanValueInequalityStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d3 := MatedCRT.coneCircleLawUniqueStep_holds
  have d4 := MatedCRT.frozenDiskGreenNonnegCont_holds
  have d5 := MatedCRT.frozenGreenBallCentre_holds
  have d6 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d7 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d8 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d9 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d10 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d11 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d12 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d11)
  closed_5_3_clean (𝒮 := 𝒮) (ν := ν) (hC := hC) (hBG := hBG) (hND := hND) (hstd := hstd) (hCentre := d5) (hOpen := d9)
    (hSup := d10) (hCons := d7) (hMono := d8) (hCompat := d6) (hBdry := hBdry) (hExist := hExist) (hThm11 := d12)
    (hProp56 := d11) (hconf := hconf) (hI2 := hI2) (hK := hK) (hloc := hloc) (hE := d2) (hFL := d1) (hE1 := d3)
    (hE2 := hE2) (hF3 := d4) (hscale := hscale) (hfirst := hfirst)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_6_1_lp_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with the inputs supplied which follow from its other inputs: `h27 : VolumeGrowthStmt` by `MatedCRT.volumeGrowthStmt_of_berestyckiGwynne`, `hmodel : FPWholePlaneLQGModel` by `MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `h611 : VeryGoodAnnulusHarnackTypeStmt.{0}` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hBdry : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `h0 : FPWholePlaneLQGExistence` by `MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `h2 : FPWholePlaneLQGCoordinateChange` by `MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_6_1_lp_noSup_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
    (h82 : TypicalPointManyGoodScalesStmt.{0})
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hV : FPWholePlaneUpperVolumeTail) :
    IDLAUpperBoundStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d3 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d4 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  have d5 := MatedCRT.coneCircleLawUniqueStep_holds
  have d6 := MatedCRT.frozenGreenBallCentre_holds
  have d7 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only (hI2 := hI2)
  have d8 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d9 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d10 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d11 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d12 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d13 := MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence (hE := d2)
  have d14 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d15 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d16 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d14)
  have d17 := MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint (hI2 := hI2) (h82 := h82)
  closed_6_1_lp_noSup (𝒮 := 𝒮) (ν := ν) (hC := hC) (h27 := d15) (hmodel := d13) (hFL := d1) (hstd := hstd)
    (hCentre := d6) (hconf := hconf) (hK := hK) (hE := d2) (hE1 := d5) (hE2 := hE2) (hscale := hscale) (hND := hND)
    (hcanon := hcanon) (hOpen := d11) (h611 := d7) (h82 := h82) (hI2 := hI2) (hSup := d12) (hCons := d9)
    (hMono := d10) (hCompat := d8) (hBdry := d17) (hExist := hExist) (hThm11 := d16) (hProp56 := d14) (hloc := hloc)
    (hBG := hBG) (h0 := d4) (h2 := d3) (hV := hV)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_6_4_lp` (MatedCRT/FirstPass/Closure/CleanSec456LP.lean) with the inputs supplied which follow from its other inputs: `h0 : FPWholePlaneLQGExistence` by `MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `h2 : FPWholePlaneLQGCoordinateChange` by `MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_6_4_lp_derivedInputs
    (hV : FPWholePlaneUpperVolumeTail) :
    FirstPass64.GoodAnnulusPrevalenceUniformStmt :=
  have d1 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d2 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  closed_6_4_lp (h0 := d2) (h2 := d1) (hV := hV)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_6_10_lp` (MatedCRT/FirstPass/Closure/CleanSec456LP.lean) with the inputs supplied which follow from its other inputs: `h0 : FPWholePlaneLQGExistence` by `MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `h2 : FPWholePlaneLQGCoordinateChange` by `MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_6_10_lp_derivedInputs
    (𝒮 : SpaceFillingSLEModel)
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hV : FPWholePlaneUpperVolumeTail) :
    IterativeBoundStmt 𝒮 :=
  have d1 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d2 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  closed_6_10_lp (𝒮 := 𝒮) (ν := ν) (hC := hC) (hBG := hBG) (h0 := d2) (h2 := d1) (hV := hV)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_7_1_lp` (MatedCRT/FirstPass/Closure/Clean61And71LP.lean) with the inputs supplied which follow from its other inputs: `h0 : FPWholePlaneLQGExistence` by `MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `h2 : FPWholePlaneLQGCoordinateChange` by `MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`, `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56HB : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_7_1_lp_derivedInputs
    (𝒮 : SpaceFillingSLEModel)
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hV : FPWholePlaneUpperVolumeTail)
    (hscale : QuantumConeScalingInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hBdryHB : ClusterBoundaryMeasureZeroStmt.{0})
    (hExistHB : ExistenceHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hlocHB : HarmonicBallLocalSetStmt.{0})
    (hE2 : ConeReferenceExistsStep)
    (hrescale : ConeRescaledMeasureIsConeFieldInput) :
    DivSandpileUpperBoundStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d3 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d4 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  have d5 := MatedCRT.coneCircleLawUniqueStep_holds
  have d6 := MatedCRT.frozenGreenBallCentre_holds
  have d7 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2HB)
  have d8 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2HB)
  have d9 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2HB)
  have d10 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2HB)
  have d11 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2HB)
  have d12 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2HB)
  have d13 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExistHB) (h56 := d12)
  closed_7_1_lp (𝒮 := 𝒮) (ν := ν) (hC := hC) (hBG := hBG) (h0 := d4) (h2 := d3) (hV := hV) (hscale := hscale)
    (hND := hND) (hstd := hstd) (hGBC := d6) (h32 := d10) (hSup := d11) (hCons := d8) (hMono := d9) (hCompat := d7)
    (hBdryHB := hBdryHB) (hExistHB := hExistHB) (hThm11 := d13) (hProp56HB := d12) (hconf := hconf) (hI2HB := hI2HB)
    (hK := hK) (hlocHB := hlocHB) (hE := d2) (hFL := d1) (hE1 := d5) (hE2 := hE2) (hrescale := hrescale)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_8_1_lp_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with the inputs supplied which follow from its other inputs: `hm : MepsScalingInput 𝒮` by `MatedCRT.CertifiedReferenceModel.mepsScaling`, `h210 : DegreeMeasureConvergenceStmt 𝒮` by `MatedCRT.CertifiedReferenceModel.degreeMeasureConvergence`, `h34 : IntegralConvergenceGreenFunctionStmt 𝒮` by `MatedCRT.closed_3_4`, `h214 : GreenKernelUpperBoundStmt 𝒮` by `MatedCRT.CertifiedReferenceModel.greenKernelUpperBound`, `h28 : CellSizeEstimateStmt 𝒮` by `MatedCRT.CertifiedReferenceModel.cellSizeEstimate`, `h35c : DiscreteDirichletProblemCorrectedStmt 𝒮` by `MatedCRT.Phase2.closed_3_5_p2`, `h218 : ExitTimeUpperBoundStmt 𝒮` by `MatedCRT.CertifiedReferenceModel.exitTimeUpperBound`, `hH : FrozenDiscreteHolderContinuityCorrected 𝒮` by `MatedCRT.CertifiedReferenceModel.frozenDiscreteHolderContinuityCorrected`, `hcone : FrozenConeScalingLaw 𝒮` by `MatedCRT.CertifiedReferenceModel.frozenConeScaling`, `h23 : ConeHarmonicBallsStmt` by `MatedCRT.coneHarmonicBalls_of_numbered_results`, `h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt` by `MatedCRT.coneHarmonicBallsUpToFixedTimeCorrected_of_canonical`, `h33 : UniformConvergenceGreenKernelStmt 𝒮` by `MatedCRT.closed_3_3`, `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hBdry : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `h27 : VolumeGrowthStmt` by `MatedCRT.volumeGrowthStmt_of_berestyckiGwynne`, `hmodel : FPWholePlaneLQGModel` by `MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence`, `h611 : VeryGoodAnnulusHarnackTypeStmt.{0}` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only`, `h0 : FPWholePlaneLQGExistence` by `MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `h2 : FPWholePlaneLQGCoordinateChange` by `MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_8_1_lp_noSup_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
    (h82 : TypicalPointManyGoodScalesStmt.{0})
    (hV : FPWholePlaneUpperVolumeTail) :
    IDLAConstrainedConvergenceStmt 𝒮 :=
  have d1 := HarmonicBalls.firstPass_2_3
  have d2 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d3 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d4 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d5 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  have d6 := MatedCRT.HBRewire.FrozenGreenDiscPole_of_hb
  have d7 := MatedCRT.coneCircleAverageLocalityStep_proved
  have d8 := MatedCRT.coneCircleLawUniqueStep_holds
  have d9 := MatedCRT.frozenGreenBallCentre_holds
  have d10 := MatedCRT.frozenLQGTestIntegralMeasurable_holds
  have d11 := MatedCRT.frozenSuperharmonicMinimumPrinciple_holds
  have d12 := MatedCRT.frozenUniversalMeasurabilityOfAnalytic_holds
  have d13 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only (hI2 := hI2)
  have d14 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d15 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d16 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d17 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d18 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d19 := MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence (hE := d3)
  have d20 := MatedCRT.LQGMeasure.coneFieldScalingStep_proved_radial (hscale := hscale)
  have d21 := MatedCRT.LQGMeasure.lqgMeasureDilationCovariancePart_of_nonDyadic (hND := hND)
  have d22 := MatedCRT.coneScaleRadiusPosStep_of_input (hscale := hscale)
  have d23 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d24 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d25 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d23)
  have d26 := MatedCRT.LQGMeasure.coneLQGScalingStep_of_dilation (hIV := d21) (hpos := d22)
  have d27 := MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint (hI2 := hI2) (h82 := h82)
  have d28 := MatedCRT.CertifiedReferenceModel.cellSizeEstimate (h := hC)
  have d29 := MatedCRT.CertifiedReferenceModel.degreeMeasureConvergence (h := hC)
  have d30 := MatedCRT.CertifiedReferenceModel.exitTimeUpperBound (h := hC)
  have d31 := MatedCRT.CertifiedReferenceModel.frozenConeScaling (h := hC)
  have d32 := MatedCRT.CertifiedReferenceModel.frozenDiscreteHolderContinuityCorrected (h := hC)
  have d33 := MatedCRT.CertifiedReferenceModel.greenKernelUpperBound (h := hC)
  have d34 := MatedCRT.CertifiedReferenceModel.mepsScaling (h := hC)
  have d35 := MatedCRT.LQGMeasure.lqgMeasureNonAtomicPart_of_scaling (h27 := d24) (hfield := d20) (hlqg := d26)
  have d36 := MatedCRT.LQGMeasure.lqgMeasureProperties_of_citedInputs (hNA := d35) (hCL := d7) (hND := hND)
  have d37 := MatedCRT.Phase2.closed_3_5_p2 (ν := ν) (hC := hC) (h27 := d24)
  have d38 := MatedCRT.closed_3_3 (ν := ν) (hC := hC) (h27 := d24)
  have d39 := MatedCRT.closed_3_4 (ν := ν) (hC := hC) (h27 := d24)
  have d40 := MatedCRT.FirstPassClosure.coneHalfBallClosureInsideStep_proof (hI2 := hI2) (hK := hK) (hloc := hloc)
    (hEx := hExist) (hE := d3) (hFL := d2) (hBG := hBG)
  have d41 := MatedCRT.sourceHalfBallPathwiseStep_of_draft (hOpen := d17) (hSup := d18) (hCons := d15) (hMono := d16)
    (hCompat := d14) (hBdry := d27) (hExist := hExist) (hThm11 := d25) (hProp56 := d23) (hconf := hconf)
  have d42 := MatedCRT.coneHalfBallGood_of_source_sep (hU := d12) (hmeasT := d10) (hsrc := d41) (hstd := hstd)
  have d43 := MatedCRT.coneCanonicalHalfBallStep_of_good (hgood := d42) (hmin := d11) (hC := d9) (hGB := d1)
    (hpole := d6)
  have d44 := MatedCRT.firstPass_2_4_canonical_of_inputs (hU := d12) (hmeasT := d10) (hsrc := d41) (hstd := hstd)
    (hmin := d11) (hC := d9) (hGB := d1) (hpole := d6) (hcl := d40) (h27 := d24)
  have d45 := MatedCRT.coneHarmonicBallsUpToFixedTimeCorrected_of_canonical (h := d44)
  have d46 := MatedCRT.coneHarmonicBallsUpToFixedTimeStmt_of_canonical (hcan := d43) (hcl := d40)
  have d47 := MatedCRT.coneRescaledHalfBallHorizonUnique_fp (hcan := d43) (hcl := d40) (hrescale := hrescale)
  have d48 := MatedCRT.coneCanonicalFactor_proved (hcan := d43) (hcl := d40) (h27 := d24) (hE1 := d8) (hE2 := hE2)
  have d49 := MatedCRT.firstPass_2_5_canonical_of_factor (hfac := d48) (hscale := hscale) (h22 := d36)
  have d50 := MatedCRT.coneScaleInvarianceUpToFixedTimeStmt_of_canonical (hcan := d43) (hcl := d40) (hc25 := d49)
    (hU := d47)
  have d51 := MatedCRT.coneHarmonicBalls_of_numbered_results (h24 := d46) (h25 := d50) (h27 := d24) (hscale := hscale)
    (h22 := d36)
  closed_8_1_lp_noSup (𝒮 := 𝒮) (ν := ν) (hC := hC) (hm := d34) (h210 := d29) (h34 := d39) (h214 := d33) (h28 := d28)
    (h35c := d37) (h218 := d30) (hH := d32) (hcone := d31) (h23 := d51) (h24c := d45) (h33 := d38) (hstd := hstd)
    (hCentre := d9) (hOpen := d17) (hSup := d18) (hCons := d15) (hMono := d16) (hCompat := d14) (hBdry := d27)
    (hExist := hExist) (hThm11 := d25) (hProp56 := d23) (hconf := hconf) (hI2 := hI2) (hK := hK) (hloc := hloc)
    (hE := d3) (hFL := d2) (hBG := hBG) (hE1 := d8) (hE2 := hE2) (hscale := hscale) (hND := hND)
    (hrescale := hrescale) (h27 := d24) (hmodel := d19) (hcanon := hcanon) (h611 := d13) (h82 := h82) (h0 := d5)
    (h2 := d4) (hV := hV)

end MatedCRT

namespace MatedCRT.FirstPass64


/-- The counted theorem `MatedCRT.FirstPass64.firstPass_6_5_uniform` (MatedCRT/FirstPass/S6q.lean) with the inputs supplied which follow from its other inputs: `h0 : FPWholePlaneLQGExistence` by `MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `h2 : FPWholePlaneLQGCoordinateChange` by `MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem firstPass_6_5_uniform_derivedInputs
    (hV : FPWholePlaneUpperVolumeTail) :
    AnnulusHitUniformStmt :=
  have d1 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d2 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  firstPass_6_5_uniform (h0 := d2) (h2 := d1) (hV := hV)

end MatedCRT.FirstPass64

namespace MatedCRT.LIClosed68Y

open MeasureTheory

/-- The counted theorem `MatedCRT.LIClosed68Y.firstPass_6_7` (MatedCRT/FirstPass/LIClosed68Y.lean) with the inputs supplied which follow from its other inputs: `hB1 : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem firstPass_6_7_derivedInputs
    {ν : ℝ → Measure SLEPathCode}
    {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence)
    (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    FaithfulConstantOrderLowerBoundStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  firstPass_6_7 (ν := ν) (𝒮 := 𝒮) (hCRM := hCRM) (hLit := hLit) (hBM := hBM) (hCC := hCC) (hB1 := d1) (hμ := hμ)
    (hBG := hBG)

end MatedCRT.LIClosed68Y

namespace MatedCRT.LIClosed68Y

open MeasureTheory

/-- The counted theorem `MatedCRT.LIClosed68Y.firstPass_6_8` (MatedCRT/FirstPass/LIClosed68Y.lean) with the inputs supplied which follow from its other inputs: `hB1 : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem firstPass_6_8_derivedInputs
    {ν : ℝ → Measure SLEPathCode}
    {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence)
    (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    FaithfulConstantOrderLowerBoundDivStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  firstPass_6_8 (ν := ν) (𝒮 := 𝒮) (hCRM := hCRM) (hLit := hLit) (hBM := hBM) (hCC := hCC) (hB1 := d1) (hμ := hμ)
    (hBG := hBG)

end MatedCRT.LIClosed68Y

namespace MatedCRT.LIClosed68Y

open MeasureTheory

/-- The counted theorem `MatedCRT.LIClosed68Y.firstPass_6_9` (MatedCRT/FirstPass/LIClosed68Y.lean) with the inputs supplied which follow from its other inputs: `hB1 : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem firstPass_6_9_derivedInputs
    {ν : ℝ → Measure SLEPathCode}
    {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence)
    (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    FaithfulChanceOfBeingAbsorbedStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  firstPass_6_9 (ν := ν) (𝒮 := 𝒮) (hCRM := hCRM) (hLit := hLit) (hBM := hBM) (hCC := hCC) (hB1 := d1) (hμ := hμ)
    (hBG := hBG)

end MatedCRT.LIClosed68Y
