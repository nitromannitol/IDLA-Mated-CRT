import HarmonicBalls.Assembly.ExistenceUniqueness
import HarmonicBalls.Proofs.Sec3.Basic
import HarmonicBalls.Proofs.Sec3.ClusterCompatibility
import HarmonicBalls.Proofs.Sec3.ConservationOfMassLemma
import HarmonicBalls.Proofs.Sec3.OpenLaplacian
import HarmonicBalls.Proofs.Sec6.VolumeGrowthConsequences
import MatedCRT.FirstPass.Closure.Clean2xLP
import MatedCRT.FirstPass.Closure.Clean42And5LP
import MatedCRT.FirstPass.Closure.Clean61And71LP
import MatedCRT.FirstPass.Closure.HLsRewire53
import MatedCRT.FirstPass.Closure.LssDerived
import MatedCRT.FirstPass.Derived.DiscGreenCentre

/-!
# Counted theorems with their proved inputs supplied

For each counted theorem of the paper that binds an input which is now a theorem, the wrapper
`<name>_derivedInputs` has the same conclusion and the remaining binders, and supplies the proved inputs.
The counted theorems and the frozen statements are unchanged. Proved inputs supplied here:

* `FrozenDiskGreenNonnegCont`: `MatedCRT.frozenDiskGreenNonnegCont_holds` (`MatedCRT.FirstPass.Derived.DiscGreenCentre`);
* `FrozenGreenBallCentre`: `MatedCRT.frozenGreenBallCentre_holds` (`MatedCRT.FirstPass.Derived.DiscGreenCentre`);

Inputs which are theorems of the Harmonic-Balls package applied to other inputs of the same counted theorem
(supplied only where the counted theorem binds those other inputs, so that no binder is added):

* `ClusterCompatibilityStmt.{0}`: `HarmonicBalls.clusterCompatibility_proved` from `LQGVolumeGrowthAllScalesStmt.{0}`;
* `ClusterConservationOfMassStmt.{0}`: `HarmonicBalls.clusterConservationOfMass_proved` from `LQGVolumeGrowthAllScalesStmt.{0}`;
* `ClusterMonotoneStmt.{0}`: `HarmonicBalls.clusterMonotone_proved` from `LQGVolumeGrowthAllScalesStmt.{0}`;
* `ClusterOpenLaplacianStmt.{0}`: `HarmonicBalls.clusterOpenLaplacian_proved` from `LQGVolumeGrowthAllScalesStmt.{0}`;
* `ExistenceUniquenessHarmonicBallsStmt.{0}`: `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5` from `ExistenceHarmonicBallsStmt.{0}` and `UniquenessHarmonicBallsStmt.{0}`;
* `FrozenVeryGoodAnnulusHarnackType`: `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only` from `LQGVolumeGrowthAllScalesStmt.{0}`;
* `LeastSupersolutionMemStmt.{0}`: `HarmonicBalls.leastSupersolutionMem_proved` from `LQGVolumeGrowthAllScalesStmt.{0}`;
* `VeryGoodAnnulusHarnackTypeStmt.{0}`: `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only` from `LQGVolumeGrowthAllScalesStmt.{0}`;

This file is generated from the signatures of the counted theorems; do not edit by hand.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_1_4_lp_noSC_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with its proved inputs supplied: `hF3 : FrozenDiskGreenNonnegCont` by `MatedCRT.frozenDiskGreenNonnegCont_holds`, `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved hI2HB`, `h611 : FrozenVeryGoodAnnulusHarnackType` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2HB`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved hI2HB`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved hI2HB`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved hI2HB`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved hI2HB`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 hExistHB hProp56HB`. Same conclusion; the remaining binders are copied unchanged. -/
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
    (h27 : VolumeGrowthStmt)
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
    (hBdryHB : ClusterBoundaryMeasureZeroStmt.{0})
    (hExistHB : ExistenceHarmonicBallsStmt.{0})
    (hProp56HB : UniquenessHarmonicBallsStmt.{0})
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0})
    (hlocHB : HarmonicBallLocalSetStmt.{0}) :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_lp_noSC_noSup (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hscale := hscale) (hEnvS := hEnvS) (hBG := hBG)
    (h0 := h0) (h2 := h2) (hV := hV) (hdiv := hdiv) (hF3 := MatedCRT.frozenDiskGreenNonnegCont_holds) (h27 := h27)
    (hFL := hFL) (hstd := hstd) (hGBC := MatedCRT.frozenGreenBallCentre_holds) (hconf := hconf) (hK := hK) (hE := hE)
    (hE1 := hE1) (hE2 := hE2) (hG15 := hG15) (h32 := HarmonicBalls.clusterOpenLaplacian_proved hI2HB)
    (h611 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2HB) (h82 := h82)
    (hSup := HarmonicBalls.leastSupersolutionMem_proved hI2HB)
    (hCons := HarmonicBalls.clusterConservationOfMass_proved hI2HB)
    (hMono := HarmonicBalls.clusterMonotone_proved hI2HB) (hCompat := HarmonicBalls.clusterCompatibility_proved hI2HB)
    (hThm11 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 hExistHB hProp56HB) (hrescale := hrescale)
    (hND := hND) (hBdryHB := hBdryHB) (hExistHB := hExistHB) (hProp56HB := hProp56HB) (hI2HB := hI2HB)
    (hlocHB := hlocHB)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_1_6_lp_noSC_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with its proved inputs supplied: `hF3 : FrozenDiskGreenNonnegCont` by `MatedCRT.frozenDiskGreenNonnegCont_holds`, `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved hI2HB`, `h611 : FrozenVeryGoodAnnulusHarnackType` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2HB`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved hI2HB`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved hI2HB`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved hI2HB`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved hI2HB`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 hExistHB hProp56HB`. Same conclusion; the remaining binders are copied unchanged. -/
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
    (h27 : VolumeGrowthStmt)
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
    (hBdryHB : ClusterBoundaryMeasureZeroStmt.{0})
    (hExistHB : ExistenceHarmonicBallsStmt.{0})
    (hProp56HB : UniquenessHarmonicBallsStmt.{0})
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0})
    (hlocHB : HarmonicBallLocalSetStmt.{0}) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_lp_noSC_noSup (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hscale := hscale) (hEnvS := hEnvS) (hBG := hBG)
    (h0 := h0) (h2 := h2) (hV := hV) (hdiv := hdiv) (hF3 := MatedCRT.frozenDiskGreenNonnegCont_holds) (h27 := h27)
    (hFL := hFL) (hstd := hstd) (hGBC := MatedCRT.frozenGreenBallCentre_holds) (hconf := hconf) (hK := hK) (hE := hE)
    (hE1 := hE1) (hE2 := hE2) (hG15 := hG15) (h32 := HarmonicBalls.clusterOpenLaplacian_proved hI2HB)
    (h611 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2HB) (h82 := h82)
    (hSup := HarmonicBalls.leastSupersolutionMem_proved hI2HB)
    (hCons := HarmonicBalls.clusterConservationOfMass_proved hI2HB)
    (hMono := HarmonicBalls.clusterMonotone_proved hI2HB) (hCompat := HarmonicBalls.clusterCompatibility_proved hI2HB)
    (hThm11 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 hExistHB hProp56HB) (hrescale := hrescale)
    (hND := hND) (hBdryHB := hBdryHB) (hExistHB := hExistHB) (hProp56HB := hProp56HB) (hI2HB := hI2HB)
    (hlocHB := hlocHB)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_2_3_lp` (MatedCRT/FirstPass/Closure/Clean2xLP.lean) with its proved inputs supplied: `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved hI2HB`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved hI2HB`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved hI2HB`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved hI2HB`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved hI2HB`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 hExistHB hProp56HB`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_2_3_lp_derivedInputs
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hscale : QuantumConeScalingInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hBdryHB : ClusterBoundaryMeasureZeroStmt.{0})
    (hExistHB : ExistenceHarmonicBallsStmt.{0})
    (hProp56HB : UniquenessHarmonicBallsStmt.{0})
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
  closed_2_3_lp (hBG := hBG) (hscale := hscale) (hND := hND) (hstd := hstd)
    (hGBC := MatedCRT.frozenGreenBallCentre_holds) (h32 := HarmonicBalls.clusterOpenLaplacian_proved hI2HB)
    (hSup := HarmonicBalls.leastSupersolutionMem_proved hI2HB)
    (hCons := HarmonicBalls.clusterConservationOfMass_proved hI2HB)
    (hMono := HarmonicBalls.clusterMonotone_proved hI2HB) (hCompat := HarmonicBalls.clusterCompatibility_proved hI2HB)
    (hBdryHB := hBdryHB) (hExistHB := hExistHB)
    (hThm11 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 hExistHB hProp56HB) (hProp56HB := hProp56HB)
    (hconf := hconf) (hI2HB := hI2HB) (hK := hK) (hlocHB := hlocHB) (hE := hE) (hFL := hFL) (hE1 := hE1) (hE2 := hE2)
    (hrescale := hrescale)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_2_4_lp` (MatedCRT/FirstPass/Closure/Clean2xLP.lean) with its proved inputs supplied: `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved hI2`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved hI2`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved hI2`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved hI2`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved hI2`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 hExist hProp56`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_2_4_lp_derivedInputs
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw)
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    ConeHarmonicBallsUpToFixedTimeCanonicalStmt :=
  closed_2_4_lp (hstd := hstd) (hCentre := MatedCRT.frozenGreenBallCentre_holds)
    (hOpen := HarmonicBalls.clusterOpenLaplacian_proved hI2) (hSup := HarmonicBalls.leastSupersolutionMem_proved hI2)
    (hCons := HarmonicBalls.clusterConservationOfMass_proved hI2) (hMono := HarmonicBalls.clusterMonotone_proved hI2)
    (hCompat := HarmonicBalls.clusterCompatibility_proved hI2) (hBdry := hBdry) (hExist := hExist)
    (hThm11 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 hExist hProp56) (hProp56 := hProp56)
    (hconf := hconf) (hI2 := hI2) (hK := hK) (hloc := hloc) (hE := hE) (hFL := hFL) (hBG := hBG)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_2_5_lp` (MatedCRT/FirstPass/Closure/Clean2xLP.lean) with its proved inputs supplied: `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved hI2`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved hI2`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved hI2`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved hI2`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved hI2`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 hExist hProp56`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_2_5_lp_derivedInputs
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
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
    (hND : LQGMeasureNonDyadicDilationPart) :
    ConeScaleInvarianceUpToFixedTimeCanonicalStmt :=
  closed_2_5_lp (hstd := hstd) (hCentre := MatedCRT.frozenGreenBallCentre_holds)
    (hOpen := HarmonicBalls.clusterOpenLaplacian_proved hI2) (hSup := HarmonicBalls.leastSupersolutionMem_proved hI2)
    (hCons := HarmonicBalls.clusterConservationOfMass_proved hI2) (hMono := HarmonicBalls.clusterMonotone_proved hI2)
    (hCompat := HarmonicBalls.clusterCompatibility_proved hI2) (hBdry := hBdry) (hExist := hExist)
    (hThm11 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 hExist hProp56) (hProp56 := hProp56)
    (hconf := hconf) (hI2 := hI2) (hK := hK) (hloc := hloc) (hE := hE) (hFL := hFL) (hBG := hBG) (hE1 := hE1)
    (hE2 := hE2) (hscale := hscale) (hND := hND)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_2_6_lp` (MatedCRT/FirstPass/Closure/Clean2xLP.lean) with its proved inputs supplied: `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved hI2`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved hI2`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved hI2`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved hI2`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved hI2`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 hExist hProp56`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_2_6_lp_derivedInputs
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
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
    (hND : LQGMeasureNonDyadicDilationPart) :
    ConeScaleInvarianceStmt :=
  closed_2_6_lp (hstd := hstd) (hCentre := MatedCRT.frozenGreenBallCentre_holds)
    (hOpen := HarmonicBalls.clusterOpenLaplacian_proved hI2) (hSup := HarmonicBalls.leastSupersolutionMem_proved hI2)
    (hCons := HarmonicBalls.clusterConservationOfMass_proved hI2) (hMono := HarmonicBalls.clusterMonotone_proved hI2)
    (hCompat := HarmonicBalls.clusterCompatibility_proved hI2) (hBdry := hBdry) (hExist := hExist)
    (hThm11 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 hExist hProp56) (hProp56 := hProp56)
    (hconf := hconf) (hI2 := hI2) (hK := hK) (hloc := hloc) (hE := hE) (hFL := hFL) (hBG := hBG) (hE1 := hE1)
    (hE2 := hE2) (hscale := hscale) (hND := hND)

end MatedCRT

namespace MatedCRT.FirstPassClosure

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.FirstPassClosure.closed_4_2_lp` (MatedCRT/FirstPass/Closure/Clean42And5LP.lean) with its proved inputs supplied: `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved hI2`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved hI2`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved hI2`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved hI2`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved hI2`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 hExist hProp56`. Same conclusion; the remaining binders are copied unchanged. -/
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
    (h23 : ConeHarmonicBallsStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
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
  closed_4_2_lp (𝒮 := 𝒮) (hm := hm) (h210 := h210) (h34 := h34) (h214 := h214) (h28 := h28) (h35c := h35c)
    (h218 := h218) (hH := hH) (hcone := hcone) (h23 := h23) (h24c := h24c) (h33 := h33) (hstd := hstd)
    (hCentre := MatedCRT.frozenGreenBallCentre_holds) (hOpen := HarmonicBalls.clusterOpenLaplacian_proved hI2)
    (hSup := HarmonicBalls.leastSupersolutionMem_proved hI2)
    (hCons := HarmonicBalls.clusterConservationOfMass_proved hI2) (hMono := HarmonicBalls.clusterMonotone_proved hI2)
    (hCompat := HarmonicBalls.clusterCompatibility_proved hI2) (hBdry := hBdry) (hExist := hExist)
    (hThm11 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 hExist hProp56) (hProp56 := hProp56)
    (hconf := hconf) (hI2 := hI2) (hK := hK) (hloc := hloc) (hE := hE) (hFL := hFL) (hBG := hBG) (hE1 := hE1)
    (hE2 := hE2) (hscale := hscale) (hND := hND) (hrescale := hrescale)

end MatedCRT.FirstPassClosure

namespace MatedCRT.FirstPassClosure

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.FirstPassClosure.closed_5_1_lp_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with its proved inputs supplied: `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved hI2`, `h611 : VeryGoodAnnulusHarnackTypeStmt.{0}` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved hI2`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved hI2`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved hI2`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved hI2`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 hEx hProp56`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_5_1_lp_noSup_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (h27 : VolumeGrowthStmt)
    (hmodel : FPWholePlaneLQGModel)
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
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hEx : ExistenceHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hSC : ClusterStrongCompatibilityStmt.{0})
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    IDLALowerBoundStmt 𝒮 :=
  closed_5_1_lp_noSup (𝒮 := 𝒮) (ν := ν) (hC := hC) (h27 := h27) (hmodel := hmodel) (hFL := hFL) (hstd := hstd)
    (hGBC := MatedCRT.frozenGreenBallCentre_holds) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2)
    (hscale := hscale) (hND := hND) (hcanon := hcanon) (h32 := HarmonicBalls.clusterOpenLaplacian_proved hI2)
    (h611 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) (h82 := h82) (hI2 := hI2)
    (hSup := HarmonicBalls.leastSupersolutionMem_proved hI2)
    (hCons := HarmonicBalls.clusterConservationOfMass_proved hI2) (hMono := HarmonicBalls.clusterMonotone_proved hI2)
    (hCompat := HarmonicBalls.clusterCompatibility_proved hI2) (hBdry := hBdry) (hEx := hEx)
    (hThm11 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 hEx hProp56) (hProp56 := hProp56)
    (hloc := hloc) (hSC := hSC) (hBG := hBG)

end MatedCRT.FirstPassClosure

namespace MatedCRT

open MeasureTheory
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_5_3_clean` (MatedCRT/FirstPass/Closure/HLsRewire53.lean) with its proved inputs supplied: `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved hI2`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved hI2`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved hI2`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved hI2`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved hI2`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 hExist hProp56`, `hF3 : FrozenDiskGreenNonnegCont` by `MatedCRT.frozenDiskGreenNonnegCont_holds`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_5_3_clean_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
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
  closed_5_3_clean (𝒮 := 𝒮) (ν := ν) (hC := hC) (hBG := hBG) (hND := hND) (hstd := hstd)
    (hCentre := MatedCRT.frozenGreenBallCentre_holds) (hOpen := HarmonicBalls.clusterOpenLaplacian_proved hI2)
    (hSup := HarmonicBalls.leastSupersolutionMem_proved hI2)
    (hCons := HarmonicBalls.clusterConservationOfMass_proved hI2) (hMono := HarmonicBalls.clusterMonotone_proved hI2)
    (hCompat := HarmonicBalls.clusterCompatibility_proved hI2) (hBdry := hBdry) (hExist := hExist)
    (hThm11 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 hExist hProp56) (hProp56 := hProp56)
    (hconf := hconf) (hI2 := hI2) (hK := hK) (hloc := hloc) (hE := hE) (hFL := hFL) (hE1 := hE1) (hE2 := hE2)
    (hF3 := MatedCRT.frozenDiskGreenNonnegCont_holds) (hscale := hscale) (hfirst := hfirst)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_6_1_lp_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with its proved inputs supplied: `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved hI2`, `h611 : VeryGoodAnnulusHarnackTypeStmt.{0}` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved hI2`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved hI2`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved hI2`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved hI2`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 hExist hProp56`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_6_1_lp_noSup_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (h27 : VolumeGrowthStmt)
    (hmodel : FPWholePlaneLQGModel)
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
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail) :
    IDLAUpperBoundStmt 𝒮 :=
  closed_6_1_lp_noSup (𝒮 := 𝒮) (ν := ν) (hC := hC) (h27 := h27) (hmodel := hmodel) (hFL := hFL) (hstd := hstd)
    (hCentre := MatedCRT.frozenGreenBallCentre_holds) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2)
    (hscale := hscale) (hND := hND) (hcanon := hcanon) (hOpen := HarmonicBalls.clusterOpenLaplacian_proved hI2)
    (h611 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) (h82 := h82) (hI2 := hI2)
    (hSup := HarmonicBalls.leastSupersolutionMem_proved hI2)
    (hCons := HarmonicBalls.clusterConservationOfMass_proved hI2) (hMono := HarmonicBalls.clusterMonotone_proved hI2)
    (hCompat := HarmonicBalls.clusterCompatibility_proved hI2) (hBdry := hBdry) (hExist := hExist)
    (hThm11 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 hExist hProp56) (hProp56 := hProp56)
    (hloc := hloc) (hBG := hBG) (h0 := h0) (h2 := h2) (hV := hV)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_7_1_lp` (MatedCRT/FirstPass/Closure/Clean61And71LP.lean) with its proved inputs supplied: `hGBC : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `h32 : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved hI2HB`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved hI2HB`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved hI2HB`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved hI2HB`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved hI2HB`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 hExistHB hProp56HB`. Same conclusion; the remaining binders are copied unchanged. -/
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
    (hProp56HB : UniquenessHarmonicBallsStmt.{0})
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
  closed_7_1_lp (𝒮 := 𝒮) (ν := ν) (hC := hC) (hBG := hBG) (h0 := h0) (h2 := h2) (hV := hV) (hscale := hscale)
    (hND := hND) (hstd := hstd) (hGBC := MatedCRT.frozenGreenBallCentre_holds)
    (h32 := HarmonicBalls.clusterOpenLaplacian_proved hI2HB)
    (hSup := HarmonicBalls.leastSupersolutionMem_proved hI2HB)
    (hCons := HarmonicBalls.clusterConservationOfMass_proved hI2HB)
    (hMono := HarmonicBalls.clusterMonotone_proved hI2HB) (hCompat := HarmonicBalls.clusterCompatibility_proved hI2HB)
    (hBdryHB := hBdryHB) (hExistHB := hExistHB)
    (hThm11 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 hExistHB hProp56HB) (hProp56HB := hProp56HB)
    (hconf := hconf) (hI2HB := hI2HB) (hK := hK) (hlocHB := hlocHB) (hE := hE) (hFL := hFL) (hE1 := hE1) (hE2 := hE2)
    (hrescale := hrescale)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The counted theorem `MatedCRT.closed_8_1_lp_noSup` (MatedCRT/FirstPass/Closure/LssDerived.lean) with its proved inputs supplied: `hCentre : FrozenGreenBallCentre` by `MatedCRT.frozenGreenBallCentre_holds`, `hOpen : ClusterOpenLaplacianStmt.{0}` by `HarmonicBalls.clusterOpenLaplacian_proved hI2`, `hSup : LeastSupersolutionMemStmt.{0}` by `HarmonicBalls.leastSupersolutionMem_proved hI2`, `hCons : ClusterConservationOfMassStmt.{0}` by `HarmonicBalls.clusterConservationOfMass_proved hI2`, `hMono : ClusterMonotoneStmt.{0}` by `HarmonicBalls.clusterMonotone_proved hI2`, `hCompat : ClusterCompatibilityStmt.{0}` by `HarmonicBalls.clusterCompatibility_proved hI2`, `hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}` by `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 hExist hProp56`, `h611 : VeryGoodAnnulusHarnackTypeStmt.{0}` by `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2`. Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_8_1_lp_noSup_derivedInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hm : MepsScalingInput 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮)
    (h35c : DiscreteDirichletProblemCorrectedStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (hcone : FrozenConeScalingLaw 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
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
    (h27 : VolumeGrowthStmt)
    (hmodel : FPWholePlaneLQGModel)
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
    (h82 : TypicalPointManyGoodScalesStmt.{0})
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail) :
    IDLAConstrainedConvergenceStmt 𝒮 :=
  closed_8_1_lp_noSup (𝒮 := 𝒮) (ν := ν) (hC := hC) (hm := hm) (h210 := h210) (h34 := h34) (h214 := h214) (h28 := h28)
    (h35c := h35c) (h218 := h218) (hH := hH) (hcone := hcone) (h23 := h23) (h24c := h24c) (h33 := h33) (hstd := hstd)
    (hCentre := MatedCRT.frozenGreenBallCentre_holds) (hOpen := HarmonicBalls.clusterOpenLaplacian_proved hI2)
    (hSup := HarmonicBalls.leastSupersolutionMem_proved hI2)
    (hCons := HarmonicBalls.clusterConservationOfMass_proved hI2) (hMono := HarmonicBalls.clusterMonotone_proved hI2)
    (hCompat := HarmonicBalls.clusterCompatibility_proved hI2) (hBdry := hBdry) (hExist := hExist)
    (hThm11 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 hExist hProp56) (hProp56 := hProp56)
    (hconf := hconf) (hI2 := hI2) (hK := hK) (hloc := hloc) (hE := hE) (hFL := hFL) (hBG := hBG) (hE1 := hE1)
    (hE2 := hE2) (hscale := hscale) (hND := hND) (hrescale := hrescale) (h27 := h27) (hmodel := hmodel)
    (hcanon := hcanon) (h611 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2)
    (h82 := h82) (h0 := h0) (h2 := h2) (hV := hV)

end MatedCRT
