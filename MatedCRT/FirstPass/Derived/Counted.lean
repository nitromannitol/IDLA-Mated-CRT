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
import MatedCRT.FirstPass.Derived.ConeLogLocalCodeLawStdDerived
import MatedCRT.FirstPass.Derived.ConeRadialDivergence
import MatedCRT.FirstPass.Derived.ConeReferenceExistsDerived
import MatedCRT.FirstPass.Derived.ConeWholePlaneFieldLaw
import MatedCRT.FirstPass.Derived.CoordChangeZero
import MatedCRT.FirstPass.Derived.DiscGreenCentre
import MatedCRT.FirstPass.Derived.HarmonicBallsVolumeGrowth
import MatedCRT.FirstPass.Derived.InsertionCoordinateRule
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

/-- The counted theorem `MatedCRT.closed_1_4_lp_noSC_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with the inputs supplied which follow from its other inputs: `h0 : FPWholePlaneLQGExistence` by `MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `h2 : FPWholePlaneLQGCoordinateChange` by `MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`, `hdiv : FrozenConeRadialDivergenceCorrected` by `MatedCRT.frozenConeRadialDivergenceCorrected_holds`, `hF3 : FrozenDiskGreenNonnegCont` by `MatedCRT.frozenDiskGreenNonnegCont_holds`, `h27 : VolumeGrowthStmt` by `MatedCRT.volumeGrowthStmt_of_berestyckiGwynne`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `h611 : FrozenVeryGoodAnnulusHarnackType` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hBdryHB : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint`, `hProp56HB : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_1_4_lp_noSC_noSup_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hV : FPWholePlaneUpperVolumeTail)
    (hconf : FrozenHBInitialConfinement)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hExistHB : ExistenceHarmonicBallsStmt.{0})
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0})
    (hlocHB : HarmonicBallLocalSetStmt.{0}) :
    ConvergenceOfIDLAStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d3 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d6 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d7 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  have d8 := MatedCRT.coneCircleLawUniqueStep_holds
  have d9 := MatedCRT.frozenConeRadialDivergenceCorrected_holds
  have d10 := MatedCRT.frozenDiskGreenNonnegCont_holds
  have d11 := MatedCRT.frozenGreenBallCentre_holds
  have d12 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only (hI2 := hI2HB)
  have d13 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2HB)
  have d14 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2HB)
  have d15 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2HB)
  have d16 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2HB)
  have d17 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2HB)
  have d18 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2HB)
  have d19 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d20 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExistHB) (h56 := d18)
  have d21 := MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint (hI2 := hI2HB) (h82 := h82)
  closed_1_4_lp_noSC_noSup (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hscale := hscale) (hEnvS := hEnvS) (hBG := hBG)
    (h0 := d7) (h2 := d6) (hV := hV) (hdiv := d9) (hF3 := d10) (h27 := d19) (hFL := d1) (hstd := d3) (hGBC := d11)
    (hconf := hconf) (hK := d4) (hE := d5) (hE1 := d8) (hE2 := d2) (hG15 := hG15) (h32 := d16) (h611 := d12)
    (h82 := h82) (hSup := d17) (hCons := d14) (hMono := d15) (hCompat := d13) (hThm11 := d20) (hrescale := hrescale)
    (hND := hND) (hBdryHB := d21) (hExistHB := hExistHB) (hProp56HB := d18) (hI2HB := hI2HB) (hlocHB := hlocHB)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_1_6_lp_noSC_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with the inputs supplied which follow from its other inputs: `h0 : FPWholePlaneLQGExistence` by `MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `h2 : FPWholePlaneLQGCoordinateChange` by `MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`, `hdiv : FrozenConeRadialDivergenceCorrected` by `MatedCRT.frozenConeRadialDivergenceCorrected_holds`, `hF3 : FrozenDiskGreenNonnegCont` by `MatedCRT.frozenDiskGreenNonnegCont_holds`, `h27 : VolumeGrowthStmt` by `MatedCRT.volumeGrowthStmt_of_berestyckiGwynne`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `h611 : FrozenVeryGoodAnnulusHarnackType` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hBdryHB : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint`, `hProp56HB : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_1_6_lp_noSC_noSup_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hV : FPWholePlaneUpperVolumeTail)
    (hconf : FrozenHBInitialConfinement)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hExistHB : ExistenceHarmonicBallsStmt.{0})
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0})
    (hlocHB : HarmonicBallLocalSetStmt.{0}) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d3 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d6 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d7 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  have d8 := MatedCRT.coneCircleLawUniqueStep_holds
  have d9 := MatedCRT.frozenConeRadialDivergenceCorrected_holds
  have d10 := MatedCRT.frozenDiskGreenNonnegCont_holds
  have d11 := MatedCRT.frozenGreenBallCentre_holds
  have d12 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only (hI2 := hI2HB)
  have d13 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2HB)
  have d14 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2HB)
  have d15 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2HB)
  have d16 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2HB)
  have d17 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2HB)
  have d18 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2HB)
  have d19 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d20 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExistHB) (h56 := d18)
  have d21 := MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint (hI2 := hI2HB) (h82 := h82)
  closed_1_6_lp_noSC_noSup (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hscale := hscale) (hEnvS := hEnvS) (hBG := hBG)
    (h0 := d7) (h2 := d6) (hV := hV) (hdiv := d9) (hF3 := d10) (h27 := d19) (hFL := d1) (hstd := d3) (hGBC := d11)
    (hconf := hconf) (hK := d4) (hE := d5) (hE1 := d8) (hE2 := d2) (hG15 := hG15) (h32 := d16) (h611 := d12)
    (h82 := h82) (hSup := d17) (hCons := d14) (hMono := d15) (hCompat := d13) (hThm11 := d20) (hrescale := hrescale)
    (hND := hND) (hBdryHB := d21) (hExistHB := hExistHB) (hProp56HB := d18) (hI2HB := hI2HB) (hlocHB := hlocHB)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_2_3_lp` (MatedCRT/FirstPass/Closure/Clean2xLP.lean) with the inputs supplied which follow from its other inputs: `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56HB : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_2_3_lp_derivedInputs
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hscale : QuantumConeScalingInput)
    (hND : LQGMeasureNonDyadicDilationPart)
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
  have d6 := MatedCRT.coneCircleLawUniqueStep_holds
  have d7 := MatedCRT.frozenGreenBallCentre_holds
  have d8 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2HB)
  have d9 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2HB)
  have d10 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2HB)
  have d11 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2HB)
  have d12 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2HB)
  have d13 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2HB)
  have d14 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExistHB) (h56 := d13)
  closed_2_3_lp (hBG := hBG) (hscale := hscale) (hND := hND) (hstd := d3) (hGBC := d7) (h32 := d11) (hSup := d12)
    (hCons := d9) (hMono := d10) (hCompat := d8) (hBdryHB := hBdryHB) (hExistHB := hExistHB) (hThm11 := d14)
    (hProp56HB := d13) (hconf := hconf) (hI2HB := hI2HB) (hK := d4) (hlocHB := hlocHB) (hE := d5) (hFL := d1)
    (hE1 := d6) (hE2 := d2) (hrescale := hrescale)

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

/-- The counted theorem `MatedCRT.closed_2_5_lp` (MatedCRT/FirstPass/Closure/Clean2xLP.lean) with the inputs supplied which follow from its other inputs: `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_2_5_lp_derivedInputs
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hscale : QuantumConeScalingInput)
    (hND : LQGMeasureNonDyadicDilationPart) :
    ConeScaleInvarianceUpToFixedTimeCanonicalStmt :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d3 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d6 := MatedCRT.coneCircleLawUniqueStep_holds
  have d7 := MatedCRT.frozenGreenBallCentre_holds
  have d8 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d9 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d10 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d11 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d12 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d13 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d14 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d13)
  closed_2_5_lp (hstd := d3) (hCentre := d7) (hOpen := d11) (hSup := d12) (hCons := d9) (hMono := d10) (hCompat := d8)
    (hBdry := hBdry) (hExist := hExist) (hThm11 := d14) (hProp56 := d13) (hconf := hconf) (hI2 := hI2) (hK := d4)
    (hloc := hloc) (hE := d5) (hFL := d1) (hBG := hBG) (hE1 := d6) (hE2 := d2) (hscale := hscale) (hND := hND)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_2_6_lp` (MatedCRT/FirstPass/Closure/Clean2xLP.lean) with the inputs supplied which follow from its other inputs: `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_2_6_lp_derivedInputs
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hscale : QuantumConeScalingInput)
    (hND : LQGMeasureNonDyadicDilationPart) :
    ConeScaleInvarianceStmt :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d3 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d6 := MatedCRT.coneCircleLawUniqueStep_holds
  have d7 := MatedCRT.frozenGreenBallCentre_holds
  have d8 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d9 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d10 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d11 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d12 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d13 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d14 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d13)
  closed_2_6_lp (hstd := d3) (hCentre := d7) (hOpen := d11) (hSup := d12) (hCons := d9) (hMono := d10) (hCompat := d8)
    (hBdry := hBdry) (hExist := hExist) (hThm11 := d14) (hProp56 := d13) (hconf := hconf) (hI2 := hI2) (hK := d4)
    (hloc := hloc) (hE := d5) (hFL := d1) (hBG := hBG) (hE1 := d6) (hE2 := d2) (hscale := hscale) (hND := hND)

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

/-- The counted theorem `MatedCRT.FirstPassClosure.closed_4_2_lp` (MatedCRT/FirstPass/Closure/Clean42And5LP.lean) with the inputs supplied which follow from its other inputs: `h23 : ConeHarmonicBallsStmt` by `MatedCRT.coneHarmonicBalls_of_numbered_results`, `h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt` by `MatedCRT.coneHarmonicBallsUpToFixedTimeCorrected_of_canonical`, `h33 : UniformConvergenceGreenKernelStmt 𝒮` by `MatedCRT.Audit.StatementsSec3Sec5M1.three_three_final_reduction`, `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`. Same conclusion; the remaining binders are copied unchanged. -/
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
    (hND : LQGMeasureNonDyadicDilationPart)
    (hrescale : ConeRescaledMeasureIsConeFieldInput) :
    DivSandpileLowerBoundStmt 𝒮 :=
  have d1 := HarmonicBalls.firstPass_2_3
  have d2 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d3 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d6 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d7 := MatedCRT.HBRewire.FrozenGreenDiscPole_of_hb
  have d8 := MatedCRT.coneCircleAverageLocalityStep_proved
  have d9 := MatedCRT.coneCircleLawUniqueStep_holds
  have d10 := MatedCRT.frozenGreenBallCentre_holds
  have d11 := MatedCRT.frozenLQGTestIntegralMeasurable_holds
  have d12 := MatedCRT.frozenSuperharmonicMinimumPrinciple_holds
  have d13 := MatedCRT.frozenUniversalMeasurabilityOfAnalytic_holds
  have d14 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d15 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d16 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d17 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d18 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d19 := MatedCRT.LQGMeasure.coneFieldScalingStep_proved_radial (hscale := hscale)
  have d20 := MatedCRT.LQGMeasure.lqgMeasureDilationCovariancePart_of_nonDyadic (hND := hND)
  have d21 := MatedCRT.coneScaleRadiusPosStep_of_input (hscale := hscale)
  have d22 := MatedCRT.firstPass_2_17_ownBinders (hBG := hBG)
  have d23 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d24 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d25 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d23)
  have d26 := MatedCRT.LQGMeasure.coneLQGScalingStep_of_dilation (hIV := d20) (hpos := d21)
  have d27 := MatedCRT.LQGMeasure.lqgMeasureNonAtomicPart_of_scaling (h27 := d24) (hfield := d19) (hlqg := d26)
  have d28 := MatedCRT.LQGMeasure.lqgMeasureProperties_of_citedInputs (hNA := d27) (hCL := d8) (hND := hND)
  have d29 := MatedCRT.discretePotentialTightnessAeStep_of_inputs (hm := hm) (h217 := d22) (h218 := h218) (hH := hH)
  have d30 := MatedCRT.Audit.StatementsSec3Sec5M1.three_three_final_reduction (𝒮 := 𝒮) (h210 := h210) (h34 := h34)
    (h214 := h214) (h28 := h28) (hAe := d29)
  have d31 := MatedCRT.FirstPassClosure.coneHalfBallClosureInsideStep_proof (hI2 := hI2) (hK := d5) (hloc := hloc)
    (hEx := hExist) (hE := d6) (hFL := d2) (hBG := hBG)
  have d32 := MatedCRT.sourceHalfBallPathwiseStep_of_draft (hOpen := d17) (hSup := d18) (hCons := d15) (hMono := d16)
    (hCompat := d14) (hBdry := hBdry) (hExist := hExist) (hThm11 := d25) (hProp56 := d23) (hconf := hconf)
  have d33 := MatedCRT.coneHalfBallGood_of_source_sep (hU := d13) (hmeasT := d11) (hsrc := d32) (hstd := d4)
  have d34 := MatedCRT.coneCanonicalHalfBallStep_of_good (hgood := d33) (hmin := d12) (hC := d10) (hGB := d1)
    (hpole := d7)
  have d35 := MatedCRT.firstPass_2_4_canonical_of_inputs (hU := d13) (hmeasT := d11) (hsrc := d32) (hstd := d4)
    (hmin := d12) (hC := d10) (hGB := d1) (hpole := d7) (hcl := d31) (h27 := d24)
  have d36 := MatedCRT.coneHarmonicBallsUpToFixedTimeCorrected_of_canonical (h := d35)
  have d37 := MatedCRT.coneHarmonicBallsUpToFixedTimeStmt_of_canonical (hcan := d34) (hcl := d31)
  have d38 := MatedCRT.coneRescaledHalfBallHorizonUnique_fp (hcan := d34) (hcl := d31) (hrescale := hrescale)
  have d39 := MatedCRT.coneCanonicalFactor_proved (hcan := d34) (hcl := d31) (h27 := d24) (hE1 := d9) (hE2 := d3)
  have d40 := MatedCRT.firstPass_2_5_canonical_of_factor (hfac := d39) (hscale := hscale) (h22 := d28)
  have d41 := MatedCRT.coneScaleInvarianceUpToFixedTimeStmt_of_canonical (hcan := d34) (hcl := d31) (hc25 := d40)
    (hU := d38)
  have d42 := MatedCRT.coneHarmonicBalls_of_numbered_results (h24 := d37) (h25 := d41) (h27 := d24) (hscale := hscale)
    (h22 := d28)
  closed_4_2_lp (𝒮 := 𝒮) (hm := hm) (h210 := h210) (h34 := h34) (h214 := h214) (h28 := h28) (h35c := h35c)
    (h218 := h218) (hH := hH) (hcone := hcone) (h23 := d42) (h24c := d36) (h33 := d30) (hstd := d4) (hCentre := d10)
    (hOpen := d17) (hSup := d18) (hCons := d15) (hMono := d16) (hCompat := d14) (hBdry := hBdry) (hExist := hExist)
    (hThm11 := d25) (hProp56 := d23) (hconf := hconf) (hI2 := hI2) (hK := d5) (hloc := hloc) (hE := d6) (hFL := d2)
    (hBG := hBG) (hE1 := d9) (hE2 := d3) (hscale := hscale) (hND := hND) (hrescale := hrescale)

end MatedCRT.FirstPassClosure

namespace MatedCRT.FirstPassClosure

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.FirstPassClosure.closed_5_1_lp_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with the inputs supplied which follow from its other inputs: `h27 : VolumeGrowthStmt` by `MatedCRT.volumeGrowthStmt_of_berestyckiGwynne`, `hmodel : FPWholePlaneLQGModel` by `MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `h611 : VeryGoodAnnulusHarnackTypeStmt.{0}` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hBdry : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hSC : ClusterStrongCompatibilityStmt.{0}` by `HarmonicBalls.clusterStrongCompatibilityStmt_of_volumeGrowth`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_5_1_lp_noSup_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hconf : FrozenHBInitialConfinement)
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
  have d2 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d3 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d6 := MatedCRT.coneCircleLawUniqueStep_holds
  have d7 := MatedCRT.frozenGreenBallCentre_holds
  have d8 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only (hI2 := hI2)
  have d9 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d10 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d11 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d12 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d13 := HarmonicBalls.clusterStrongCompatibilityStmt_of_volumeGrowth (hI2 := hI2)
  have d14 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d15 := MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence (hE := d5)
  have d16 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d17 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d18 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hEx) (h56 := d16)
  have d19 := MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint (hI2 := hI2) (h82 := h82)
  closed_5_1_lp_noSup (𝒮 := 𝒮) (ν := ν) (hC := hC) (h27 := d17) (hmodel := d15) (hFL := d1) (hstd := d3) (hGBC := d7)
    (hconf := hconf) (hK := d4) (hE := d5) (hE1 := d6) (hE2 := d2) (hscale := hscale) (hND := hND) (hcanon := hcanon)
    (h32 := d12) (h611 := d8) (h82 := h82) (hI2 := hI2) (hSup := d14) (hCons := d10) (hMono := d11) (hCompat := d9)
    (hBdry := d19) (hEx := hEx) (hThm11 := d18) (hProp56 := d16) (hloc := hloc) (hSC := d13) (hBG := hBG)

end MatedCRT.FirstPassClosure

namespace MatedCRT

open MeasureTheory
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_5_3_clean` (MatedCRT/FirstPass/Closure/HLsRewire53.lean) with the inputs supplied which follow from its other inputs: `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`, `hF3 : FrozenDiskGreenNonnegCont` by `MatedCRT.frozenDiskGreenNonnegCont_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_5_3_clean_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hND : LQGMeasureNonDyadicDilationPart)
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
  have d6 := MatedCRT.coneCircleLawUniqueStep_holds
  have d7 := MatedCRT.frozenDiskGreenNonnegCont_holds
  have d8 := MatedCRT.frozenGreenBallCentre_holds
  have d9 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d10 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d11 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d12 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d13 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d14 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d15 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d14)
  closed_5_3_clean (𝒮 := 𝒮) (ν := ν) (hC := hC) (hBG := hBG) (hND := hND) (hstd := d3) (hCentre := d8) (hOpen := d12)
    (hSup := d13) (hCons := d10) (hMono := d11) (hCompat := d9) (hBdry := hBdry) (hExist := hExist) (hThm11 := d15)
    (hProp56 := d14) (hconf := hconf) (hI2 := hI2) (hK := d4) (hloc := hloc) (hE := d5) (hFL := d1) (hE1 := d6)
    (hE2 := d2) (hF3 := d7) (hscale := hscale) (hfirst := hfirst)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_6_1_lp_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with the inputs supplied which follow from its other inputs: `h27 : VolumeGrowthStmt` by `MatedCRT.volumeGrowthStmt_of_berestyckiGwynne`, `hmodel : FPWholePlaneLQGModel` by `MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `h611 : VeryGoodAnnulusHarnackTypeStmt.{0}` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hBdry : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `h0 : FPWholePlaneLQGExistence` by `MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `h2 : FPWholePlaneLQGCoordinateChange` by `MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_6_1_lp_noSup_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hconf : FrozenHBInitialConfinement)
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
  have d2 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d3 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d6 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d7 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  have d8 := MatedCRT.coneCircleLawUniqueStep_holds
  have d9 := MatedCRT.frozenGreenBallCentre_holds
  have d10 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only (hI2 := hI2)
  have d11 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d12 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d13 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d14 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d15 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d16 := MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence (hE := d5)
  have d17 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d18 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d19 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d17)
  have d20 := MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint (hI2 := hI2) (h82 := h82)
  closed_6_1_lp_noSup (𝒮 := 𝒮) (ν := ν) (hC := hC) (h27 := d18) (hmodel := d16) (hFL := d1) (hstd := d3)
    (hCentre := d9) (hconf := hconf) (hK := d4) (hE := d5) (hE1 := d8) (hE2 := d2) (hscale := hscale) (hND := hND)
    (hcanon := hcanon) (hOpen := d14) (h611 := d10) (h82 := h82) (hI2 := hI2) (hSup := d15) (hCons := d12)
    (hMono := d13) (hCompat := d11) (hBdry := d20) (hExist := hExist) (hThm11 := d19) (hProp56 := d17) (hloc := hloc)
    (hBG := hBG) (h0 := d7) (h2 := d6) (hV := hV)

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

/-- The counted theorem `MatedCRT.closed_7_1_lp` (MatedCRT/FirstPass/Closure/Clean61And71LP.lean) with the inputs supplied which follow from its other inputs: `h0 : FPWholePlaneLQGExistence` by `MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `h2 : FPWholePlaneLQGCoordinateChange` by `MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`, `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56HB : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_7_1_lp_derivedInputs
    (𝒮 : SpaceFillingSLEModel)
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hV : FPWholePlaneUpperVolumeTail)
    (hscale : QuantumConeScalingInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hBdryHB : ClusterBoundaryMeasureZeroStmt.{0})
    (hExistHB : ExistenceHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0})
    (hlocHB : HarmonicBallLocalSetStmt.{0})
    (hrescale : ConeRescaledMeasureIsConeFieldInput) :
    DivSandpileUpperBoundStmt 𝒮 :=
  have d1 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d2 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d3 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d6 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d7 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  have d8 := MatedCRT.coneCircleLawUniqueStep_holds
  have d9 := MatedCRT.frozenGreenBallCentre_holds
  have d10 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2HB)
  have d11 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2HB)
  have d12 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2HB)
  have d13 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2HB)
  have d14 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2HB)
  have d15 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2HB)
  have d16 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExistHB) (h56 := d15)
  closed_7_1_lp (𝒮 := 𝒮) (ν := ν) (hC := hC) (hBG := hBG) (h0 := d7) (h2 := d6) (hV := hV) (hscale := hscale)
    (hND := hND) (hstd := d3) (hGBC := d9) (h32 := d13) (hSup := d14) (hCons := d11) (hMono := d12) (hCompat := d10)
    (hBdryHB := hBdryHB) (hExistHB := hExistHB) (hThm11 := d16) (hProp56HB := d15) (hconf := hconf) (hI2HB := hI2HB)
    (hK := d4) (hlocHB := hlocHB) (hE := d5) (hFL := d1) (hE1 := d8) (hE2 := d2) (hrescale := hrescale)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_8_1_lp_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with the inputs supplied which follow from its other inputs: `hm : MepsScalingInput 𝒮` by `MatedCRT.CertifiedReferenceModel.mepsScaling`, `h210 : DegreeMeasureConvergenceStmt 𝒮` by `MatedCRT.CertifiedReferenceModel.degreeMeasureConvergence`, `h34 : IntegralConvergenceGreenFunctionStmt 𝒮` by `MatedCRT.closed_3_4`, `h214 : GreenKernelUpperBoundStmt 𝒮` by `MatedCRT.CertifiedReferenceModel.greenKernelUpperBound`, `h28 : CellSizeEstimateStmt 𝒮` by `MatedCRT.CertifiedReferenceModel.cellSizeEstimate`, `h35c : DiscreteDirichletProblemCorrectedStmt 𝒮` by `MatedCRT.Phase2.closed_3_5_p2`, `h218 : ExitTimeUpperBoundStmt 𝒮` by `MatedCRT.CertifiedReferenceModel.exitTimeUpperBound`, `hH : FrozenDiscreteHolderContinuityCorrected 𝒮` by `MatedCRT.CertifiedReferenceModel.frozenDiscreteHolderContinuityCorrected`, `hcone : FrozenConeScalingLaw 𝒮` by `MatedCRT.CertifiedReferenceModel.frozenConeScaling`, `h23 : ConeHarmonicBallsStmt` by `MatedCRT.coneHarmonicBalls_of_numbered_results`, `h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt` by `MatedCRT.coneHarmonicBallsUpToFixedTimeCorrected_of_canonical`, `h33 : UniformConvergenceGreenKernelStmt 𝒮` by `MatedCRT.closed_3_3`, `hstd : FrozenConeLogLocalCodeLawStd` by `MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds`, `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hBdry : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hK : FirstPass.S2k.FrozenInsertionCoordinateRule` by `MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds`, `hE : FirstPass.S2m.FrozenLQGMeasureExistenceInsertion` by `MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds`, `hFL : FPConeWholePlaneFieldLaw` by `MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds`, `hE1 : ConeCircleLawUniqueStep` by `MatedCRT.coneCircleLawUniqueStep_holds`, `hE2 : ConeReferenceExistsStep` by `MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds`, `h27 : VolumeGrowthStmt` by `MatedCRT.volumeGrowthStmt_of_berestyckiGwynne`, `hmodel : FPWholePlaneLQGModel` by `MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence`, `h611 : VeryGoodAnnulusHarnackTypeStmt.{0}` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only`, `h0 : FPWholePlaneLQGExistence` by `MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds`, `h2 : FPWholePlaneLQGCoordinateChange` by `MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds`. Same conclusion; the remaining binders are copied unchanged. -/
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
    (hND : LQGMeasureNonDyadicDilationPart)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
    (h82 : TypicalPointManyGoodScalesStmt.{0})
    (hV : FPWholePlaneUpperVolumeTail) :
    IDLAConstrainedConvergenceStmt 𝒮 :=
  have d1 := HarmonicBalls.firstPass_2_3
  have d2 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d3 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d6 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d7 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d8 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  have d9 := MatedCRT.HBRewire.FrozenGreenDiscPole_of_hb
  have d10 := MatedCRT.coneCircleAverageLocalityStep_proved
  have d11 := MatedCRT.coneCircleLawUniqueStep_holds
  have d12 := MatedCRT.frozenGreenBallCentre_holds
  have d13 := MatedCRT.frozenLQGTestIntegralMeasurable_holds
  have d14 := MatedCRT.frozenSuperharmonicMinimumPrinciple_holds
  have d15 := MatedCRT.frozenUniversalMeasurabilityOfAnalytic_holds
  have d16 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only (hI2 := hI2)
  have d17 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d18 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d19 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d20 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d21 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d22 := MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence (hE := d6)
  have d23 := MatedCRT.LQGMeasure.coneFieldScalingStep_proved_radial (hscale := hscale)
  have d24 := MatedCRT.LQGMeasure.lqgMeasureDilationCovariancePart_of_nonDyadic (hND := hND)
  have d25 := MatedCRT.coneScaleRadiusPosStep_of_input (hscale := hscale)
  have d26 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d27 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d28 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d26)
  have d29 := MatedCRT.LQGMeasure.coneLQGScalingStep_of_dilation (hIV := d24) (hpos := d25)
  have d30 := MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint (hI2 := hI2) (h82 := h82)
  have d31 := MatedCRT.CertifiedReferenceModel.cellSizeEstimate (h := hC)
  have d32 := MatedCRT.CertifiedReferenceModel.degreeMeasureConvergence (h := hC)
  have d33 := MatedCRT.CertifiedReferenceModel.exitTimeUpperBound (h := hC)
  have d34 := MatedCRT.CertifiedReferenceModel.frozenConeScaling (h := hC)
  have d35 := MatedCRT.CertifiedReferenceModel.frozenDiscreteHolderContinuityCorrected (h := hC)
  have d36 := MatedCRT.CertifiedReferenceModel.greenKernelUpperBound (h := hC)
  have d37 := MatedCRT.CertifiedReferenceModel.mepsScaling (h := hC)
  have d38 := MatedCRT.LQGMeasure.lqgMeasureNonAtomicPart_of_scaling (h27 := d27) (hfield := d23) (hlqg := d29)
  have d39 := MatedCRT.LQGMeasure.lqgMeasureProperties_of_citedInputs (hNA := d38) (hCL := d10) (hND := hND)
  have d40 := MatedCRT.Phase2.closed_3_5_p2 (ν := ν) (hC := hC) (h27 := d27)
  have d41 := MatedCRT.closed_3_3 (ν := ν) (hC := hC) (h27 := d27)
  have d42 := MatedCRT.closed_3_4 (ν := ν) (hC := hC) (h27 := d27)
  have d43 := MatedCRT.FirstPassClosure.coneHalfBallClosureInsideStep_proof (hI2 := hI2) (hK := d5) (hloc := hloc)
    (hEx := hExist) (hE := d6) (hFL := d2) (hBG := hBG)
  have d44 := MatedCRT.sourceHalfBallPathwiseStep_of_draft (hOpen := d20) (hSup := d21) (hCons := d18) (hMono := d19)
    (hCompat := d17) (hBdry := d30) (hExist := hExist) (hThm11 := d28) (hProp56 := d26) (hconf := hconf)
  have d45 := MatedCRT.coneHalfBallGood_of_source_sep (hU := d15) (hmeasT := d13) (hsrc := d44) (hstd := d4)
  have d46 := MatedCRT.coneCanonicalHalfBallStep_of_good (hgood := d45) (hmin := d14) (hC := d12) (hGB := d1)
    (hpole := d9)
  have d47 := MatedCRT.firstPass_2_4_canonical_of_inputs (hU := d15) (hmeasT := d13) (hsrc := d44) (hstd := d4)
    (hmin := d14) (hC := d12) (hGB := d1) (hpole := d9) (hcl := d43) (h27 := d27)
  have d48 := MatedCRT.coneHarmonicBallsUpToFixedTimeCorrected_of_canonical (h := d47)
  have d49 := MatedCRT.coneHarmonicBallsUpToFixedTimeStmt_of_canonical (hcan := d46) (hcl := d43)
  have d50 := MatedCRT.coneRescaledHalfBallHorizonUnique_fp (hcan := d46) (hcl := d43) (hrescale := hrescale)
  have d51 := MatedCRT.coneCanonicalFactor_proved (hcan := d46) (hcl := d43) (h27 := d27) (hE1 := d11) (hE2 := d3)
  have d52 := MatedCRT.firstPass_2_5_canonical_of_factor (hfac := d51) (hscale := hscale) (h22 := d39)
  have d53 := MatedCRT.coneScaleInvarianceUpToFixedTimeStmt_of_canonical (hcan := d46) (hcl := d43) (hc25 := d52)
    (hU := d50)
  have d54 := MatedCRT.coneHarmonicBalls_of_numbered_results (h24 := d49) (h25 := d53) (h27 := d27) (hscale := hscale)
    (h22 := d39)
  closed_8_1_lp_noSup (𝒮 := 𝒮) (ν := ν) (hC := hC) (hm := d37) (h210 := d32) (h34 := d42) (h214 := d36) (h28 := d31)
    (h35c := d40) (h218 := d33) (hH := d35) (hcone := d34) (h23 := d54) (h24c := d48) (h33 := d41) (hstd := d4)
    (hCentre := d12) (hOpen := d20) (hSup := d21) (hCons := d18) (hMono := d19) (hCompat := d17) (hBdry := d30)
    (hExist := hExist) (hThm11 := d28) (hProp56 := d26) (hconf := hconf) (hI2 := hI2) (hK := d5) (hloc := hloc)
    (hE := d6) (hFL := d2) (hBG := hBG) (hE1 := d11) (hE2 := d3) (hscale := hscale) (hND := hND)
    (hrescale := hrescale) (h27 := d27) (hmodel := d22) (hcanon := hcanon) (h611 := d16) (h82 := h82) (h0 := d8)
    (h2 := d7) (hV := hV)

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
