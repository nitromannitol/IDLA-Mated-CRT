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
import MatedCRT.FirstPass.Closure.HLsRewire53
import MatedCRT.FirstPass.Closure.LssDerived
import MatedCRT.FirstPass.Closure.OwnBinderRewire
import MatedCRT.FirstPass.Closure.Section3
import MatedCRT.FirstPass.Closure.Steps42
import MatedCRT.FirstPass.Derived.DiscGreenCentre
import MatedCRT.FirstPass.Derived.HarmonicBallsVolumeGrowth
import MatedCRT.FirstPass.HBRewire
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

/-- The counted theorem `MatedCRT.closed_1_4_lp_noSC_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with the inputs supplied which follow from its other inputs: `hF3 : FrozenDiskGreenNonnegCont` by `MatedCRT.frozenDiskGreenNonnegCont_holds`, `h27 : VolumeGrowthStmt` by `MatedCRT.volumeGrowthStmt_of_berestyckiGwynne`, `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `h611 : FrozenVeryGoodAnnulusHarnackType` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hBdryHB : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint`, `hProp56HB : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_1_4_lp_noSC_noSup_derivedInputs
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
    (hFL : FPConeWholePlaneFieldLaw)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hExistHB : ExistenceHarmonicBallsStmt.{0})
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0})
    (hlocHB : HarmonicBallLocalSetStmt.{0}) :
    ConvergenceOfIDLAStmt 𝒮 :=
  have d1 := MatedCRT.frozenDiskGreenNonnegCont_holds
  have d2 := MatedCRT.frozenGreenBallCentre_holds
  have d3 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only (hI2 := hI2HB)
  have d4 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2HB)
  have d5 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2HB)
  have d6 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2HB)
  have d7 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2HB)
  have d8 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2HB)
  have d9 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2HB)
  have d10 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d11 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExistHB) (h56 := d9)
  have d12 := MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint (hI2 := hI2HB) (h82 := h82)
  closed_1_4_lp_noSC_noSup (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hscale := hscale) (hEnvS := hEnvS) (hBG := hBG)
    (h0 := h0) (h2 := h2) (hV := hV) (hdiv := hdiv) (hF3 := d1) (h27 := d10) (hFL := hFL) (hstd := hstd) (hGBC := d2)
    (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (hG15 := hG15) (h32 := d7) (h611 := d3)
    (h82 := h82) (hSup := d8) (hCons := d5) (hMono := d6) (hCompat := d4) (hThm11 := d11) (hrescale := hrescale)
    (hND := hND) (hBdryHB := d12) (hExistHB := hExistHB) (hProp56HB := d9) (hI2HB := hI2HB) (hlocHB := hlocHB)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_1_6_lp_noSC_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with the inputs supplied which follow from its other inputs: `hF3 : FrozenDiskGreenNonnegCont` by `MatedCRT.frozenDiskGreenNonnegCont_holds`, `h27 : VolumeGrowthStmt` by `MatedCRT.volumeGrowthStmt_of_berestyckiGwynne`, `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `h611 : FrozenVeryGoodAnnulusHarnackType` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hBdryHB : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint`, `hProp56HB : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_1_6_lp_noSC_noSup_derivedInputs
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
    (hFL : FPConeWholePlaneFieldLaw)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hExistHB : ExistenceHarmonicBallsStmt.{0})
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0})
    (hlocHB : HarmonicBallLocalSetStmt.{0}) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  have d1 := MatedCRT.frozenDiskGreenNonnegCont_holds
  have d2 := MatedCRT.frozenGreenBallCentre_holds
  have d3 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only (hI2 := hI2HB)
  have d4 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2HB)
  have d5 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2HB)
  have d6 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2HB)
  have d7 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2HB)
  have d8 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2HB)
  have d9 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2HB)
  have d10 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d11 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExistHB) (h56 := d9)
  have d12 := MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint (hI2 := hI2HB) (h82 := h82)
  closed_1_6_lp_noSC_noSup (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hscale := hscale) (hEnvS := hEnvS) (hBG := hBG)
    (h0 := h0) (h2 := h2) (hV := hV) (hdiv := hdiv) (hF3 := d1) (h27 := d10) (hFL := hFL) (hstd := hstd) (hGBC := d2)
    (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (hG15 := hG15) (h32 := d7) (h611 := d3)
    (h82 := h82) (hSup := d8) (hCons := d5) (hMono := d6) (hCompat := d4) (hThm11 := d11) (hrescale := hrescale)
    (hND := hND) (hBdryHB := d12) (hExistHB := hExistHB) (hProp56HB := d9) (hI2HB := hI2HB) (hlocHB := hlocHB)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_2_3_lp` (MatedCRT/FirstPass/Closure/Clean2xLP.lean) with the inputs supplied which follow from its other inputs: `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56HB : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`. Same conclusion; the remaining binders are copied unchanged. -/
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
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hrescale : ConeRescaledMeasureIsConeFieldInput) :
    ConeHarmonicBallsStmt :=
  have d1 := MatedCRT.frozenGreenBallCentre_holds
  have d2 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2HB)
  have d3 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2HB)
  have d4 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2HB)
  have d5 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2HB)
  have d6 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2HB)
  have d7 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2HB)
  have d8 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExistHB) (h56 := d7)
  closed_2_3_lp (hBG := hBG) (hscale := hscale) (hND := hND) (hstd := hstd) (hGBC := d1) (h32 := d5) (hSup := d6)
    (hCons := d3) (hMono := d4) (hCompat := d2) (hBdryHB := hBdryHB) (hExistHB := hExistHB) (hThm11 := d8)
    (hProp56HB := d7) (hconf := hconf) (hI2HB := hI2HB) (hK := hK) (hlocHB := hlocHB) (hE := hE) (hFL := hFL)
    (hE1 := hE1) (hE2 := hE2) (hrescale := hrescale)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_2_4_lp` (MatedCRT/FirstPass/Closure/Clean2xLP.lean) with the inputs supplied which follow from its other inputs: `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_2_4_lp_derivedInputs
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw)
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    ConeHarmonicBallsUpToFixedTimeCanonicalStmt :=
  have d1 := MatedCRT.frozenGreenBallCentre_holds
  have d2 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d3 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d4 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d5 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d6 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d7 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d8 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d7)
  closed_2_4_lp (hstd := hstd) (hCentre := d1) (hOpen := d5) (hSup := d6) (hCons := d3) (hMono := d4) (hCompat := d2)
    (hBdry := hBdry) (hExist := hExist) (hThm11 := d8) (hProp56 := d7) (hconf := hconf) (hI2 := hI2) (hK := hK)
    (hloc := hloc) (hE := hE) (hFL := hFL) (hBG := hBG)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_2_5_lp` (MatedCRT/FirstPass/Closure/Clean2xLP.lean) with the inputs supplied which follow from its other inputs: `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_2_5_lp_derivedInputs
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
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
    (hND : LQGMeasureNonDyadicDilationPart) :
    ConeScaleInvarianceUpToFixedTimeCanonicalStmt :=
  have d1 := MatedCRT.frozenGreenBallCentre_holds
  have d2 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d3 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d4 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d5 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d6 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d7 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d8 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d7)
  closed_2_5_lp (hstd := hstd) (hCentre := d1) (hOpen := d5) (hSup := d6) (hCons := d3) (hMono := d4) (hCompat := d2)
    (hBdry := hBdry) (hExist := hExist) (hThm11 := d8) (hProp56 := d7) (hconf := hconf) (hI2 := hI2) (hK := hK)
    (hloc := hloc) (hE := hE) (hFL := hFL) (hBG := hBG) (hE1 := hE1) (hE2 := hE2) (hscale := hscale) (hND := hND)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_2_6_lp` (MatedCRT/FirstPass/Closure/Clean2xLP.lean) with the inputs supplied which follow from its other inputs: `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_2_6_lp_derivedInputs
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
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
    (hND : LQGMeasureNonDyadicDilationPart) :
    ConeScaleInvarianceStmt :=
  have d1 := MatedCRT.frozenGreenBallCentre_holds
  have d2 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d3 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d4 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d5 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d6 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d7 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d8 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d7)
  closed_2_6_lp (hstd := hstd) (hCentre := d1) (hOpen := d5) (hSup := d6) (hCons := d3) (hMono := d4) (hCompat := d2)
    (hBdry := hBdry) (hExist := hExist) (hThm11 := d8) (hProp56 := d7) (hconf := hconf) (hI2 := hI2) (hK := hK)
    (hloc := hloc) (hE := hE) (hFL := hFL) (hBG := hBG) (hE1 := hE1) (hE2 := hE2) (hscale := hscale) (hND := hND)

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

/-- The counted theorem `MatedCRT.FirstPassClosure.closed_4_2_lp` (MatedCRT/FirstPass/Closure/Clean42And5LP.lean) with the inputs supplied which follow from its other inputs: `h23 : ConeHarmonicBallsStmt` by `MatedCRT.coneHarmonicBalls_of_numbered_results`, `h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt` by `MatedCRT.coneHarmonicBallsUpToFixedTimeCorrected_of_canonical`, `h33 : UniformConvergenceGreenKernelStmt 𝒮` by `MatedCRT.Audit.StatementsSec3Sec5M1.three_three_final_reduction`, `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`. Same conclusion; the remaining binders are copied unchanged. -/
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
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hrescale : ConeRescaledMeasureIsConeFieldInput) :
    DivSandpileLowerBoundStmt 𝒮 :=
  have d1 := HarmonicBalls.firstPass_2_3
  have d2 := MatedCRT.HBRewire.FrozenGreenDiscPole_of_hb
  have d3 := MatedCRT.coneCircleAverageLocalityStep_proved
  have d4 := MatedCRT.frozenGreenBallCentre_holds
  have d5 := MatedCRT.frozenLQGTestIntegralMeasurable_holds
  have d6 := MatedCRT.frozenSuperharmonicMinimumPrinciple_holds
  have d7 := MatedCRT.frozenUniversalMeasurabilityOfAnalytic_holds
  have d8 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d9 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d10 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d11 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d12 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d13 := MatedCRT.LQGMeasure.coneFieldScalingStep_proved_radial (hscale := hscale)
  have d14 := MatedCRT.LQGMeasure.lqgMeasureDilationCovariancePart_of_nonDyadic (hND := hND)
  have d15 := MatedCRT.coneScaleRadiusPosStep_of_input (hscale := hscale)
  have d16 := MatedCRT.firstPass_2_17_ownBinders (hBG := hBG)
  have d17 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d18 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d19 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d17)
  have d20 := MatedCRT.LQGMeasure.coneLQGScalingStep_of_dilation (hIV := d14) (hpos := d15)
  have d21 := MatedCRT.LQGMeasure.lqgMeasureNonAtomicPart_of_scaling (h27 := d18) (hfield := d13) (hlqg := d20)
  have d22 := MatedCRT.LQGMeasure.lqgMeasureProperties_of_citedInputs (hNA := d21) (hCL := d3) (hND := hND)
  have d23 := MatedCRT.discretePotentialTightnessAeStep_of_inputs (hm := hm) (h217 := d16) (h218 := h218) (hH := hH)
  have d24 := MatedCRT.Audit.StatementsSec3Sec5M1.three_three_final_reduction (𝒮 := 𝒮) (h210 := h210) (h34 := h34)
    (h214 := h214) (h28 := h28) (hAe := d23)
  have d25 := MatedCRT.FirstPassClosure.coneHalfBallClosureInsideStep_proof (hI2 := hI2) (hK := hK) (hloc := hloc)
    (hEx := hExist) (hE := hE) (hFL := hFL) (hBG := hBG)
  have d26 := MatedCRT.sourceHalfBallPathwiseStep_of_draft (hOpen := d11) (hSup := d12) (hCons := d9) (hMono := d10)
    (hCompat := d8) (hBdry := hBdry) (hExist := hExist) (hThm11 := d19) (hProp56 := d17) (hconf := hconf)
  have d27 := MatedCRT.coneHalfBallGood_of_source_sep (hU := d7) (hmeasT := d5) (hsrc := d26) (hstd := hstd)
  have d28 := MatedCRT.coneCanonicalHalfBallStep_of_good (hgood := d27) (hmin := d6) (hC := d4) (hGB := d1)
    (hpole := d2)
  have d29 := MatedCRT.firstPass_2_4_canonical_of_inputs (hU := d7) (hmeasT := d5) (hsrc := d26) (hstd := hstd)
    (hmin := d6) (hC := d4) (hGB := d1) (hpole := d2) (hcl := d25) (h27 := d18)
  have d30 := MatedCRT.coneHarmonicBallsUpToFixedTimeCorrected_of_canonical (h := d29)
  have d31 := MatedCRT.coneHarmonicBallsUpToFixedTimeStmt_of_canonical (hcan := d28) (hcl := d25)
  have d32 := MatedCRT.coneRescaledHalfBallHorizonUnique_fp (hcan := d28) (hcl := d25) (hrescale := hrescale)
  have d33 := MatedCRT.coneCanonicalFactor_proved (hcan := d28) (hcl := d25) (h27 := d18) (hE1 := hE1) (hE2 := hE2)
  have d34 := MatedCRT.firstPass_2_5_canonical_of_factor (hfac := d33) (hscale := hscale) (h22 := d22)
  have d35 := MatedCRT.coneScaleInvarianceUpToFixedTimeStmt_of_canonical (hcan := d28) (hcl := d25) (hc25 := d34)
    (hU := d32)
  have d36 := MatedCRT.coneHarmonicBalls_of_numbered_results (h24 := d31) (h25 := d35) (h27 := d18) (hscale := hscale)
    (h22 := d22)
  closed_4_2_lp (𝒮 := 𝒮) (hm := hm) (h210 := h210) (h34 := h34) (h214 := h214) (h28 := h28) (h35c := h35c)
    (h218 := h218) (hH := hH) (hcone := hcone) (h23 := d36) (h24c := d30) (h33 := d24) (hstd := hstd) (hCentre := d4)
    (hOpen := d11) (hSup := d12) (hCons := d9) (hMono := d10) (hCompat := d8) (hBdry := hBdry) (hExist := hExist)
    (hThm11 := d19) (hProp56 := d17) (hconf := hconf) (hI2 := hI2) (hK := hK) (hloc := hloc) (hE := hE) (hFL := hFL)
    (hBG := hBG) (hE1 := hE1) (hE2 := hE2) (hscale := hscale) (hND := hND) (hrescale := hrescale)

end MatedCRT.FirstPassClosure

namespace MatedCRT.FirstPassClosure

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.FirstPassClosure.closed_5_1_lp_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with the inputs supplied which follow from its other inputs: `h27 : VolumeGrowthStmt` by `MatedCRT.volumeGrowthStmt_of_berestyckiGwynne`, `hmodel : FPWholePlaneLQGModel` by `MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence`, `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `h611 : VeryGoodAnnulusHarnackTypeStmt.{0}` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hBdry : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hSC : ClusterStrongCompatibilityStmt.{0}` by `HarmonicBalls.clusterStrongCompatibilityStmt_of_volumeGrowth`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_5_1_lp_noSup_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hFL : FPConeWholePlaneFieldLaw)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
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
  have d1 := MatedCRT.frozenGreenBallCentre_holds
  have d2 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only (hI2 := hI2)
  have d3 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d4 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d5 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d6 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d7 := HarmonicBalls.clusterStrongCompatibilityStmt_of_volumeGrowth (hI2 := hI2)
  have d8 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d9 := MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence (hE := hE)
  have d10 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d11 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d12 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hEx) (h56 := d10)
  have d13 := MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint (hI2 := hI2) (h82 := h82)
  closed_5_1_lp_noSup (𝒮 := 𝒮) (ν := ν) (hC := hC) (h27 := d11) (hmodel := d9) (hFL := hFL) (hstd := hstd)
    (hGBC := d1) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (hscale := hscale) (hND := hND)
    (hcanon := hcanon) (h32 := d6) (h611 := d2) (h82 := h82) (hI2 := hI2) (hSup := d8) (hCons := d4) (hMono := d5)
    (hCompat := d3) (hBdry := d13) (hEx := hEx) (hThm11 := d12) (hProp56 := d10) (hloc := hloc) (hSC := d7)
    (hBG := hBG)

end MatedCRT.FirstPassClosure

namespace MatedCRT

open MeasureTheory
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_5_3_clean` (MatedCRT/FirstPass/Closure/HLsRewire53.lean) with the inputs supplied which follow from its other inputs: `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `hF3 : FrozenDiskGreenNonnegCont` by `MatedCRT.frozenDiskGreenNonnegCont_holds`. Same conclusion; the remaining binders are copied unchanged. -/
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
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput)
    (hfirst : FPFirstHitVisits 𝒮) :
    MeanValueInequalityStmt 𝒮 :=
  have d1 := MatedCRT.frozenDiskGreenNonnegCont_holds
  have d2 := MatedCRT.frozenGreenBallCentre_holds
  have d3 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d4 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d5 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d6 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d7 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d8 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d9 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d8)
  closed_5_3_clean (𝒮 := 𝒮) (ν := ν) (hC := hC) (hBG := hBG) (hND := hND) (hstd := hstd) (hCentre := d2) (hOpen := d6)
    (hSup := d7) (hCons := d4) (hMono := d5) (hCompat := d3) (hBdry := hBdry) (hExist := hExist) (hThm11 := d9)
    (hProp56 := d8) (hconf := hconf) (hI2 := hI2) (hK := hK) (hloc := hloc) (hE := hE) (hFL := hFL) (hE1 := hE1)
    (hE2 := hE2) (hF3 := d1) (hscale := hscale) (hfirst := hfirst)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_6_1_lp_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with the inputs supplied which follow from its other inputs: `h27 : VolumeGrowthStmt` by `MatedCRT.volumeGrowthStmt_of_berestyckiGwynne`, `hmodel : FPWholePlaneLQGModel` by `MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence`, `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `h611 : VeryGoodAnnulusHarnackTypeStmt.{0}` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hBdry : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_6_1_lp_noSup_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hFL : FPConeWholePlaneFieldLaw)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
    (h82 : TypicalPointManyGoodScalesStmt.{0})
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail) :
    IDLAUpperBoundStmt 𝒮 :=
  have d1 := MatedCRT.frozenGreenBallCentre_holds
  have d2 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only (hI2 := hI2)
  have d3 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d4 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d5 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d6 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d7 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d8 := MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence (hE := hE)
  have d9 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d10 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d11 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d9)
  have d12 := MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint (hI2 := hI2) (h82 := h82)
  closed_6_1_lp_noSup (𝒮 := 𝒮) (ν := ν) (hC := hC) (h27 := d10) (hmodel := d8) (hFL := hFL) (hstd := hstd)
    (hCentre := d1) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (hscale := hscale) (hND := hND)
    (hcanon := hcanon) (hOpen := d6) (h611 := d2) (h82 := h82) (hI2 := hI2) (hSup := d7) (hCons := d4) (hMono := d5)
    (hCompat := d3) (hBdry := d12) (hExist := hExist) (hThm11 := d11) (hProp56 := d9) (hloc := hloc) (hBG := hBG)
    (h0 := h0) (h2 := h2) (hV := hV)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_7_1_lp` (MatedCRT/FirstPass/Closure/Clean61And71LP.lean) with the inputs supplied which follow from its other inputs: `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56HB : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_7_1_lp_derivedInputs
    (𝒮 : SpaceFillingSLEModel)
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
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
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hrescale : ConeRescaledMeasureIsConeFieldInput) :
    DivSandpileUpperBoundStmt 𝒮 :=
  have d1 := MatedCRT.frozenGreenBallCentre_holds
  have d2 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2HB)
  have d3 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2HB)
  have d4 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2HB)
  have d5 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2HB)
  have d6 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2HB)
  have d7 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2HB)
  have d8 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExistHB) (h56 := d7)
  closed_7_1_lp (𝒮 := 𝒮) (ν := ν) (hC := hC) (hBG := hBG) (h0 := h0) (h2 := h2) (hV := hV) (hscale := hscale)
    (hND := hND) (hstd := hstd) (hGBC := d1) (h32 := d5) (hSup := d6) (hCons := d3) (hMono := d4) (hCompat := d2)
    (hBdryHB := hBdryHB) (hExistHB := hExistHB) (hThm11 := d8) (hProp56HB := d7) (hconf := hconf) (hI2HB := hI2HB)
    (hK := hK) (hlocHB := hlocHB) (hE := hE) (hFL := hFL) (hE1 := hE1) (hE2 := hE2) (hrescale := hrescale)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_8_1_lp_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with the inputs supplied which follow from its other inputs: `hm : MepsScalingInput 𝒮` by `MatedCRT.CertifiedReferenceModel.mepsScaling`, `h210 : DegreeMeasureConvergenceStmt 𝒮` by `MatedCRT.CertifiedReferenceModel.degreeMeasureConvergence`, `h34 : IntegralConvergenceGreenFunctionStmt 𝒮` by `MatedCRT.closed_3_4`, `h214 : GreenKernelUpperBoundStmt 𝒮` by `MatedCRT.CertifiedReferenceModel.greenKernelUpperBound`, `h28 : CellSizeEstimateStmt 𝒮` by `MatedCRT.CertifiedReferenceModel.cellSizeEstimate`, `h35c : DiscreteDirichletProblemCorrectedStmt 𝒮` by `MatedCRT.Phase2.closed_3_5_p2`, `h218 : ExitTimeUpperBoundStmt 𝒮` by `MatedCRT.CertifiedReferenceModel.exitTimeUpperBound`, `hH : FrozenDiscreteHolderContinuityCorrected 𝒮` by `MatedCRT.CertifiedReferenceModel.frozenDiscreteHolderContinuityCorrected`, `hcone : FrozenConeScalingLaw 𝒮` by `MatedCRT.CertifiedReferenceModel.frozenConeScaling`, `h23 : ConeHarmonicBallsStmt` by `MatedCRT.coneHarmonicBalls_of_numbered_results`, `h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt` by `MatedCRT.coneHarmonicBallsUpToFixedTimeCorrected_of_canonical`, `h33 : UniformConvergenceGreenKernelStmt 𝒮` by `MatedCRT.closed_3_3`, `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved`, `hBdry : ClusterBoundaryMeasureZeroStmt.{0}` by `MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5`, `hProp56 : UniquenessHarmonicBallsStmt.{0}` by `MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth`, `h27 : VolumeGrowthStmt` by `MatedCRT.volumeGrowthStmt_of_berestyckiGwynne`, `hmodel : FPWholePlaneLQGModel` by `MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence`, `h611 : VeryGoodAnnulusHarnackTypeStmt.{0}` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only`. Same conclusion; the remaining binders are copied unchanged. -/
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
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
    (h82 : TypicalPointManyGoodScalesStmt.{0})
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail) :
    IDLAConstrainedConvergenceStmt 𝒮 :=
  have d1 := HarmonicBalls.firstPass_2_3
  have d2 := MatedCRT.HBRewire.FrozenGreenDiscPole_of_hb
  have d3 := MatedCRT.coneCircleAverageLocalityStep_proved
  have d4 := MatedCRT.frozenGreenBallCentre_holds
  have d5 := MatedCRT.frozenLQGTestIntegralMeasurable_holds
  have d6 := MatedCRT.frozenSuperharmonicMinimumPrinciple_holds
  have d7 := MatedCRT.frozenUniversalMeasurabilityOfAnalytic_holds
  have d8 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only (hI2 := hI2)
  have d9 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d10 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d11 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d12 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d13 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d14 := MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence (hE := hE)
  have d15 := MatedCRT.LQGMeasure.coneFieldScalingStep_proved_radial (hscale := hscale)
  have d16 := MatedCRT.LQGMeasure.lqgMeasureDilationCovariancePart_of_nonDyadic (hND := hND)
  have d17 := MatedCRT.coneScaleRadiusPosStep_of_input (hscale := hscale)
  have d18 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d19 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d20 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d18)
  have d21 := MatedCRT.LQGMeasure.coneLQGScalingStep_of_dilation (hIV := d16) (hpos := d17)
  have d22 := MatedCRT.clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint (hI2 := hI2) (h82 := h82)
  have d23 := MatedCRT.CertifiedReferenceModel.cellSizeEstimate (h := hC)
  have d24 := MatedCRT.CertifiedReferenceModel.degreeMeasureConvergence (h := hC)
  have d25 := MatedCRT.CertifiedReferenceModel.exitTimeUpperBound (h := hC)
  have d26 := MatedCRT.CertifiedReferenceModel.frozenConeScaling (h := hC)
  have d27 := MatedCRT.CertifiedReferenceModel.frozenDiscreteHolderContinuityCorrected (h := hC)
  have d28 := MatedCRT.CertifiedReferenceModel.greenKernelUpperBound (h := hC)
  have d29 := MatedCRT.CertifiedReferenceModel.mepsScaling (h := hC)
  have d30 := MatedCRT.LQGMeasure.lqgMeasureNonAtomicPart_of_scaling (h27 := d19) (hfield := d15) (hlqg := d21)
  have d31 := MatedCRT.LQGMeasure.lqgMeasureProperties_of_citedInputs (hNA := d30) (hCL := d3) (hND := hND)
  have d32 := MatedCRT.Phase2.closed_3_5_p2 (ν := ν) (hC := hC) (h27 := d19)
  have d33 := MatedCRT.closed_3_3 (ν := ν) (hC := hC) (h27 := d19)
  have d34 := MatedCRT.closed_3_4 (ν := ν) (hC := hC) (h27 := d19)
  have d35 := MatedCRT.FirstPassClosure.coneHalfBallClosureInsideStep_proof (hI2 := hI2) (hK := hK) (hloc := hloc)
    (hEx := hExist) (hE := hE) (hFL := hFL) (hBG := hBG)
  have d36 := MatedCRT.sourceHalfBallPathwiseStep_of_draft (hOpen := d12) (hSup := d13) (hCons := d10) (hMono := d11)
    (hCompat := d9) (hBdry := d22) (hExist := hExist) (hThm11 := d20) (hProp56 := d18) (hconf := hconf)
  have d37 := MatedCRT.coneHalfBallGood_of_source_sep (hU := d7) (hmeasT := d5) (hsrc := d36) (hstd := hstd)
  have d38 := MatedCRT.coneCanonicalHalfBallStep_of_good (hgood := d37) (hmin := d6) (hC := d4) (hGB := d1)
    (hpole := d2)
  have d39 := MatedCRT.firstPass_2_4_canonical_of_inputs (hU := d7) (hmeasT := d5) (hsrc := d36) (hstd := hstd)
    (hmin := d6) (hC := d4) (hGB := d1) (hpole := d2) (hcl := d35) (h27 := d19)
  have d40 := MatedCRT.coneHarmonicBallsUpToFixedTimeCorrected_of_canonical (h := d39)
  have d41 := MatedCRT.coneHarmonicBallsUpToFixedTimeStmt_of_canonical (hcan := d38) (hcl := d35)
  have d42 := MatedCRT.coneRescaledHalfBallHorizonUnique_fp (hcan := d38) (hcl := d35) (hrescale := hrescale)
  have d43 := MatedCRT.coneCanonicalFactor_proved (hcan := d38) (hcl := d35) (h27 := d19) (hE1 := hE1) (hE2 := hE2)
  have d44 := MatedCRT.firstPass_2_5_canonical_of_factor (hfac := d43) (hscale := hscale) (h22 := d31)
  have d45 := MatedCRT.coneScaleInvarianceUpToFixedTimeStmt_of_canonical (hcan := d38) (hcl := d35) (hc25 := d44)
    (hU := d42)
  have d46 := MatedCRT.coneHarmonicBalls_of_numbered_results (h24 := d41) (h25 := d45) (h27 := d19) (hscale := hscale)
    (h22 := d31)
  closed_8_1_lp_noSup (𝒮 := 𝒮) (ν := ν) (hC := hC) (hm := d29) (h210 := d24) (h34 := d34) (h214 := d28) (h28 := d23)
    (h35c := d32) (h218 := d25) (hH := d27) (hcone := d26) (h23 := d46) (h24c := d40) (h33 := d33) (hstd := hstd)
    (hCentre := d4) (hOpen := d12) (hSup := d13) (hCons := d10) (hMono := d11) (hCompat := d9) (hBdry := d22)
    (hExist := hExist) (hThm11 := d20) (hProp56 := d18) (hconf := hconf) (hI2 := hI2) (hK := hK) (hloc := hloc)
    (hE := hE) (hFL := hFL) (hBG := hBG) (hE1 := hE1) (hE2 := hE2) (hscale := hscale) (hND := hND)
    (hrescale := hrescale) (h27 := d19) (hmodel := d14) (hcanon := hcanon) (h611 := d8) (h82 := h82) (h0 := h0)
    (h2 := h2) (hV := hV)

end MatedCRT
