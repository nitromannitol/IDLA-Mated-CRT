import HarmonicBalls.FirstPass.S2S3S4S9SA
import HarmonicBalls.Steps.SecA.Basic
import HarmonicBalls.Proofs.Sec8.GreenKernelContinuity
import MatedCRT.FirstPass.Closure.Theorem14d
import MatedCRT.FirstPass.S2g.Corrected24
import MatedCRT.FirstPass.S2g.Assembly2456
import MatedCRT.FirstPass.S4d.Final42

/-!
# Harmonic Balls rewire of the counted IDLA theorems

Namespace `MatedCRT.HBRewire`. The Harmonic-Balls inputs that HB proves unconditionally and that the counted IDLA
theorems bind are discharged here. Each counted theorem `T` gets a `T_hb` with the same conclusion and the remaining
binders; the discharged binders are passed as the `_of_hb` proofs below.
Discharged: `GreenFunctionBallStmt` (HB Prop 2.3) and `FrozenGreenDiscPole` (its MatedCRT copy, proved from the same HB
Prop 2.3 and the HB pole limit). Not discharged here (HB result conditional on literature or model inputs; see the
report): ClusterOpenLaplacian, LeastSupersolutionMem, ClusterMonotone, ClusterConservation, ClusterCompatibility,
LQGVolumeGrowthAllScales, VeryGoodAnnulusHarnackType, and the MatedCRT copies FrozenLeastSupersolutionMemCone and
FrozenLQGVolumeGrowthAllScales / FrozenVeryGoodAnnulusHarnackType.
-/

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls
open MatedCRT.FirstPassClosure

noncomputable section

namespace MatedCRT.HBRewire

/-- **Proposition 2.3 (`prop:green-properties`), Green function of a ball.** HB (Harmonic-Balls arXiv:2208.11795) proves
`HarmonicBalls.GreenFunctionBallStmt` (Draft: HarmonicBalls/Draft/Section2.lean:68) unconditionally as
`HarmonicBalls.firstPass_2_3` (HarmonicBalls/FirstPass/S2S3S4S9SA.lean:41), which is `HarmonicBalls.greenFunctionBall`
(HarmonicBalls/Steps/Sec2/GreenFunctionBall.lean:156). -/
theorem GreenFunctionBallStmt_of_hb : HarmonicBalls.GreenFunctionBallStmt :=
  HarmonicBalls.firstPass_2_3

/-- The MatedCRT copy `MatedCRT.FrozenGreenDiscPole` (MatedCRT/FirstPass/Frozen/S2g.lean:36): continuity on
`closedBall 0 R \ {0}` from `HarmonicBalls.continuousOn_greenFunction_ball_of_stmt` (HarmonicBalls/Steps/SecA/Basic.lean:165)
applied to `GreenFunctionBallStmt_of_hb`, and the pole limit `HarmonicBalls.tendsto_greenFunction_ball_pole`
(HarmonicBalls/Proofs/Sec8/GreenKernelContinuity.lean:16). -/
theorem FrozenGreenDiscPole_of_hb : FrozenGreenDiscPole := fun _ hR =>
  ⟨HarmonicBalls.continuousOn_greenFunction_ball_of_stmt GreenFunctionBallStmt_of_hb hR (Metric.mem_ball_self hR),
    HarmonicBalls.tendsto_greenFunction_ball_pole (Metric.mem_ball_self hR)⟩

/-- Counted theorem `MatedCRT.FirstPassClosure.closed_1_4_derived` (MatedCRT/FirstPass/Closure/Theorem14d.lean), with the discharged inputs hGBall:GreenFunctionBallStmt_of_hb, hpole:FrozenGreenDiscPole_of_hb supplied by the HB proofs. -/
theorem closed_1_4_derived_hb
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮)
    (hdeg : DegreeBoundInput 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h51 : BG20Prop51 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction)
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hcell : FrozenAdjacentCellsMeetAe 𝒮)
    (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮)
    (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality)
    (hpair : FPPairingLawIG4)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
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
    (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple)
    (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep)
    (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt)
    : ConvergenceOfIDLAStmt 𝒮 :=
  MatedCRT.FirstPassClosure.closed_1_4_derived (𝒮 := 𝒮) (ν := ν) (hC := hC) (hscale := hscale) (hsc := hsc) (hrp := hrp) (hind := hind) (hEnvS := hEnvS) (hm := hm) (hdeg := hdeg) (hBG := hBG) (h28 := h28) (h29 := h29) (h210 := h210) (h214 := h214) (h216 := h216) (h51 := h51) (hH := hH) (h0 := h0) (h2 := h2) (hV := hV) (hR := hR) (hcone := hcone) (hrevuz := hrevuz) (h23 := h23) (hdiv := hdiv) (hF1 := hF1) (hF2 := hF2) (hF3 := hF3) (hcell := hcell) (hexc := hexc) (hμae := hμae) (hSB := hSB) (hsup := hsup) (hmodel := hmodel) (hFL := hFL) (hLoc := hLoc) (hpair := hpair) (hstd := hstd) (hmin := hmin) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (h22 := h22) (h24c := h24c) (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc) (hSC := hSC) (hGBall := GreenFunctionBallStmt_of_hb) (hpc := hpc) (hsmp := hsmp) (hpole := FrozenGreenDiscPole_of_hb) (hnj := hnj) (hcan := hcan) (hcl := hcl) (hcan6 := hcan6)

/-- Counted theorem `MatedCRT.FirstPassClosure.closed_1_6_derived` (MatedCRT/FirstPass/Closure/Theorem14d.lean), with the discharged inputs hGBall:GreenFunctionBallStmt_of_hb, hpole:FrozenGreenDiscPole_of_hb supplied by the HB proofs. -/
theorem closed_1_6_derived_hb
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮)
    (hdeg : DegreeBoundInput 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h51 : BG20Prop51 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction)
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hcell : FrozenAdjacentCellsMeetAe 𝒮)
    (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮)
    (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality)
    (hpair : FPPairingLawIG4)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
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
    (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple)
    (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep)
    (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt)
    : ConvergenceOfDivSandpileStmt 𝒮 :=
  MatedCRT.FirstPassClosure.closed_1_6_derived (𝒮 := 𝒮) (ν := ν) (hC := hC) (hscale := hscale) (hsc := hsc) (hrp := hrp) (hind := hind) (hEnvS := hEnvS) (hm := hm) (hdeg := hdeg) (hBG := hBG) (h28 := h28) (h29 := h29) (h210 := h210) (h214 := h214) (h216 := h216) (h51 := h51) (hH := hH) (h0 := h0) (h2 := h2) (hV := hV) (hR := hR) (hcone := hcone) (hrevuz := hrevuz) (h23 := h23) (hdiv := hdiv) (hF1 := hF1) (hF2 := hF2) (hF3 := hF3) (hcell := hcell) (hexc := hexc) (hμae := hμae) (hSB := hSB) (hsup := hsup) (hmodel := hmodel) (hFL := hFL) (hLoc := hLoc) (hpair := hpair) (hstd := hstd) (hmin := hmin) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (h22 := h22) (h24c := h24c) (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc) (hSC := hSC) (hGBall := GreenFunctionBallStmt_of_hb) (hpc := hpc) (hsmp := hsmp) (hpole := FrozenGreenDiscPole_of_hb) (hnj := hnj) (hcan := hcan) (hcl := hcl) (hcan6 := hcan6)

/-- Counted theorem `MatedCRT.firstPass_2_4_canonical` (MatedCRT/FirstPass/S2g/Corrected24.lean), with the discharged inputs hGB:GreenFunctionBallStmt_of_hb, hpole:FrozenGreenDiscPole_of_hb supplied by the HB proofs. -/
theorem firstPass_2_4_canonical_hb
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hCentre : FrozenGreenBallCentre)
    (hOpen : ClusterOpenLaplacianStmt.{0})
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hSC : ClusterStrongCompatibilityStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw)
    (h27 : VolumeGrowthStmt)
    : ConeHarmonicBallsUpToFixedTimeCanonicalStmt :=
  MatedCRT.firstPass_2_4_canonical (hU := hU) (hmeasT := hmeasT) (hstd := hstd) (hmin := hmin) (hCentre := hCentre) (hGB := GreenFunctionBallStmt_of_hb) (hpole := FrozenGreenDiscPole_of_hb) (hOpen := hOpen) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hExist := hExist) (hThm11 := hThm11) (hProp56 := hProp56) (hconf := hconf) (hI2 := hI2) (hK := hK) (hloc := hloc) (hSC := hSC) (hE := hE) (hFL := hFL) (h27 := h27)

/-- Counted theorem `MatedCRT.firstPass_2_5_canonical` (MatedCRT/FirstPass/S2g/Assembly2456.lean), with the discharged inputs hGB:GreenFunctionBallStmt_of_hb, hpole:FrozenGreenDiscPole_of_hb supplied by the HB proofs. -/
theorem firstPass_2_5_canonical_hb
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hCentre : FrozenGreenBallCentre)
    (hOpen : ClusterOpenLaplacianStmt.{0})
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hSC : ClusterStrongCompatibilityStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw)
    (h27 : VolumeGrowthStmt)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput)
    (h22 : LQGMeasurePropertiesStmt)
    : ConeScaleInvarianceUpToFixedTimeCanonicalStmt :=
  MatedCRT.firstPass_2_5_canonical (hU := hU) (hmeasT := hmeasT) (hstd := hstd) (hmin := hmin) (hCentre := hCentre) (hGB := GreenFunctionBallStmt_of_hb) (hpole := FrozenGreenDiscPole_of_hb) (hOpen := hOpen) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hExist := hExist) (hThm11 := hThm11) (hProp56 := hProp56) (hconf := hconf) (hI2 := hI2) (hK := hK) (hloc := hloc) (hSC := hSC) (hE := hE) (hFL := hFL) (h27 := h27) (hE1 := hE1) (hE2 := hE2) (hscale := hscale) (h22 := h22)

/-- Counted theorem `MatedCRT.firstPass_2_6_corrected` (MatedCRT/FirstPass/S2g/Assembly2456.lean), with the discharged inputs hGB:GreenFunctionBallStmt_of_hb, hpole:FrozenGreenDiscPole_of_hb supplied by the HB proofs. -/
theorem firstPass_2_6_corrected_hb
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hCentre : FrozenGreenBallCentre)
    (hOpen : ClusterOpenLaplacianStmt.{0})
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hSC : ClusterStrongCompatibilityStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw)
    (h27 : VolumeGrowthStmt)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput)
    (h22 : LQGMeasurePropertiesStmt)
    : ConeScaleInvarianceStmt :=
  MatedCRT.firstPass_2_6_corrected (hU := hU) (hmeasT := hmeasT) (hstd := hstd) (hmin := hmin) (hCentre := hCentre) (hGB := GreenFunctionBallStmt_of_hb) (hpole := FrozenGreenDiscPole_of_hb) (hOpen := hOpen) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hExist := hExist) (hThm11 := hThm11) (hProp56 := hProp56) (hconf := hconf) (hI2 := hI2) (hK := hK) (hloc := hloc) (hSC := hSC) (hE := hE) (hFL := hFL) (h27 := h27) (hE1 := hE1) (hE2 := hE2) (hscale := hscale) (h22 := h22)

/-- Counted theorem `MatedCRT.firstPass_4_2_of_wholeplane_model` (MatedCRT/FirstPass/S4d/Final42.lean), with the discharged inputs hG:GreenFunctionBallStmt_of_hb, hpole:FrozenGreenDiscPole_of_hb supplied by the HB proofs. -/
theorem firstPass_4_2_of_wholeplane_model_hb
    {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮)
    (h36 : CorrectedHarmonicConvergenceStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h27 : VolumeGrowthStmt)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple)
    (hwmp : FrozenSuperharmonicMinimumPrinciple)
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hCentre : FrozenGreenBallCentre)
    (hOpen : ClusterOpenLaplacianStmt.{0})
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hSC : ClusterStrongCompatibilityStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : MatedCRT.FPConeWholePlaneFieldLaw)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput)
    (h22 : LQGMeasurePropertiesStmt)
    : DivSandpileLowerBoundStmt 𝒮 :=
  MatedCRT.firstPass_4_2_of_wholeplane_model (𝒮 := 𝒮) (hm := hm) (h210 := h210) (h214 := h214) (h28 := h28) (h36 := h36) (h218 := h218) (h27 := h27) (hH := hH) (hEnvS := hEnvS) (hsc := hsc) (hrp := hrp) (hind := hind) (hrevuz := hrevuz) (hdet := hdet) (hrescale := hrescale) (hG := GreenFunctionBallStmt_of_hb) (hpc := hpc) (hsmp := hsmp) (hwmp := hwmp) (hpole := FrozenGreenDiscPole_of_hb) (hU := hU) (hmeasT := hmeasT) (hstd := hstd) (hCentre := hCentre) (hOpen := hOpen) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hExist := hExist) (hThm11 := hThm11) (hProp56 := hProp56) (hconf := hconf) (hI2 := hI2) (hK := hK) (hloc := hloc) (hSC := hSC) (hE := hE) (hFL := hFL) (hE1 := hE1) (hE2 := hE2) (hscale := hscale) (h22 := h22)

#print axioms GreenFunctionBallStmt_of_hb
#print axioms FrozenGreenDiscPole_of_hb
#print axioms closed_1_4_derived_hb
#print axioms closed_1_6_derived_hb
#print axioms firstPass_2_4_canonical_hb
#print axioms firstPass_2_5_canonical_hb
#print axioms firstPass_2_6_corrected_hb
#print axioms firstPass_4_2_of_wholeplane_model_hb

end MatedCRT.HBRewire

end
