import MatedCRT.FirstPass.Frozen.S5k
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.VolumeGrowthInsideUnit
import HarmonicBalls.Steps.Sec3.LeastSupersolutionMem
import HarmonicBalls.Proofs.SecA.ObstacleNonCoincidenceHarmonic
import HarmonicBalls.Proofs.Sec3.Basic
import MatedCRT.FirstPass.Closure.Clean14And16LPNoSC
import MatedCRT.FirstPass.Closure.Clean42And5LP
import MatedCRT.FirstPass.Closure.Clean61And71LP
import MatedCRT.FirstPass.Closure.Clean81LP
import MatedCRT.FirstPass.Main
import MatedCRT.FirstPass.Closure.CellRewire

/-!
# Frozen least-supersolution input derived from the volume growth

`FrozenLeastSupersolutionMemCone` (the least supersolution lies in the cone of supersolutions)
is a theorem of `VolumeGrowthStmt` (IDLA Lemma 2.7) plus the deterministic form of the
Harnack-Ball least-supersolution lemma (HB Lemma 3.1, Armitage-Gardiner obstacle problem).
The file gives that theorem and, for each counted form that binds `hsup`, a wrapper with
`hsup` replaced by `VolumeGrowthStmt`.
-/

namespace MatedCRT

open MeasureTheory _root_.HarmonicBalls

/-- The frozen input `FrozenLeastSupersolutionMemCone` follows from `VolumeGrowthStmt`
(HB Lemma 3.1 deterministic form). -/
theorem frozenLeastSupersolutionMemCone_of_volumeGrowth (𝒮 : SpaceFillingSLEModel)
    (h27 : VolumeGrowthStmt) : FrozenLeastSupersolutionMemCone 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS
  have hn : ∀ n : ℕ, ∀ᵐ ω ∂S.P, ∃ βm βp,
      VolumeGrowth (S.μ ω) (1 - 1 / ((n : ℝ) + 1)) βm βp := fun n =>
    hS.ae_volumeGrowth_inside_unit hγ hγ2 h27
      (by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
          linarith)
  have hlf : ∀ᵐ ω ∂S.P, IsLocallyFiniteMeasure (S.μ ω) :=
    hS.isConeField.2.2.mono fun ω h => h.isLocallyFiniteMeasure
  filter_upwards [ae_all_iff.mpr hn, hlf] with ω hω hloc ρ hρ0 hρ1 t ht
  obtain ⟨n, hnρ⟩ := exists_nat_one_div_lt (sub_pos.mpr hρ1)
  obtain ⟨βm, βp, hV⟩ := hω n
  exact (leastSupersolution_mem_of_general obstacleLeastSuperharmonicMajorantGeneral_holds
    obstacleCompatibilityShiftStep_holds hloc hρ0 (hV.mono (by linarith))
    (Metric.mem_ball_self hρ0) ht).2.2

end MatedCRT

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- Result 1.4 (`closed_1_4_lp_noSC`) with hsup derived from VolumeGrowthStmt (HB Lemma 3.1 deterministic form). -/
theorem closed_1_4_lp_noSC_noSup
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
    (h27 : VolumeGrowthStmt)
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
  MatedCRT.closed_1_4_lp_noSC (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hscale := hscale) (hEnvS := hEnvS) (hBG := hBG) (h0 := h0) (h2 := h2) (hV := hV) (hdiv := hdiv) (hF3 := hF3) (hFL := hFL) (hstd := hstd) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hThm11 := hThm11) (hrescale := hrescale) (hND := hND) (hBdryHB := hBdryHB) (hExistHB := hExistHB) (hProp56HB := hProp56HB) (hI2HB := hI2HB) (hlocHB := hlocHB) (hsup := MatedCRT.frozenLeastSupersolutionMemCone_of_volumeGrowth 𝒮 h27)

/-- Result 1.6 (`closed_1_6_lp_noSC`) with hsup derived from VolumeGrowthStmt (HB Lemma 3.1 deterministic form). -/
theorem closed_1_6_lp_noSC_noSup
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
    (h27 : VolumeGrowthStmt)
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
  MatedCRT.closed_1_6_lp_noSC (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hscale := hscale) (hEnvS := hEnvS) (hBG := hBG) (h0 := h0) (h2 := h2) (hV := hV) (hdiv := hdiv) (hF3 := hF3) (hFL := hFL) (hstd := hstd) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hThm11 := hThm11) (hrescale := hrescale) (hND := hND) (hBdryHB := hBdryHB) (hExistHB := hExistHB) (hProp56HB := hProp56HB) (hI2HB := hI2HB) (hlocHB := hlocHB) (hsup := MatedCRT.frozenLeastSupersolutionMemCone_of_volumeGrowth 𝒮 h27)

/-- Result 1.4 (`firstPassMain_1_4_full`) with hsup derived from VolumeGrowthStmt (HB Lemma 3.1 deterministic form). -/
theorem firstPassMain_1_4_full_noSup
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
    (h27 : VolumeGrowthStmt)
    (hmodel : FPWholePlaneLQGModel)
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
  MatedCRT.firstPassMain_1_4_full (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hscale := hscale) (hsc := hsc) (hrp := hrp) (hind := hind) (hEnvS := hEnvS) (hBG := hBG) (h0 := h0) (h2 := h2) (hV := hV) (hdiv := hdiv) (hF3 := hF3) (hmodel := hmodel) (hFL := hFL) (hstd := hstd) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc) (hSC := hSC) (hrescale := hrescale) (hND := hND) (hBdryHB := hBdryHB) (hExistHB := hExistHB) (hProp56HB := hProp56HB) (hI2HB := hI2HB) (hlocHB := hlocHB) (hSCHB := hSCHB) (hU := hU) (hmeasT := hmeasT) (hmin := hmin) (hGB := hGB) (hpole := hpole) (hsup := MatedCRT.frozenLeastSupersolutionMemCone_of_volumeGrowth 𝒮 h27)

/-- Result 1.6 (`firstPassMain_1_6_full`) with hsup derived from VolumeGrowthStmt (HB Lemma 3.1 deterministic form). -/
theorem firstPassMain_1_6_full_noSup
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
    (h27 : VolumeGrowthStmt)
    (hmodel : FPWholePlaneLQGModel)
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
  MatedCRT.firstPassMain_1_6_full (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hscale := hscale) (hsc := hsc) (hrp := hrp) (hind := hind) (hEnvS := hEnvS) (hBG := hBG) (h0 := h0) (h2 := h2) (hV := hV) (hdiv := hdiv) (hF3 := hF3) (hmodel := hmodel) (hFL := hFL) (hstd := hstd) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc) (hSC := hSC) (hrescale := hrescale) (hND := hND) (hBdryHB := hBdryHB) (hExistHB := hExistHB) (hProp56HB := hProp56HB) (hI2HB := hI2HB) (hlocHB := hlocHB) (hSCHB := hSCHB) (hU := hU) (hmeasT := hmeasT) (hmin := hmin) (hGB := hGB) (hpole := hpole) (hsup := MatedCRT.frozenLeastSupersolutionMemCone_of_volumeGrowth 𝒮 h27)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set
open _root_.HarmonicBalls

/-- Result 6.1 (`closed_6_1_lp`) with hsup derived from VolumeGrowthStmt (HB Lemma 3.1 deterministic form). -/
theorem closed_6_1_lp_noSup
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (h27 : VolumeGrowthStmt)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hCentre : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
    (hOpen : ClusterOpenLaplacianStmt.{0})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{0})
    (h82 : TypicalPointManyGoodScalesStmt.{0})
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail) :
    IDLAUpperBoundStmt 𝒮 :=
  MatedCRT.closed_6_1_lp (𝒮 := 𝒮) (ν := ν) (hC := hC) (hmodel := hmodel) (hFL := hFL) (hstd := hstd) (hCentre := hCentre) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (hscale := hscale) (hND := hND) (hcanon := hcanon) (hOpen := hOpen) (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hExist := hExist) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc) (hBG := hBG) (h0 := h0) (h2 := h2) (hV := hV) (hsup := MatedCRT.frozenLeastSupersolutionMemCone_of_volumeGrowth 𝒮 h27)

/-- Result 8.1 (`closed_8_1_lp`) with hsup derived from VolumeGrowthStmt (HB Lemma 3.1 deterministic form). -/
theorem closed_8_1_lp_noSup
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
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{0})
    (h82 : TypicalPointManyGoodScalesStmt.{0})
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail) :
    IDLAConstrainedConvergenceStmt 𝒮 :=
  MatedCRT.closed_8_1_lp (𝒮 := 𝒮) (ν := ν) (hC := hC) (hm := hm) (h210 := h210) (h34 := h34) (h214 := h214) (h28 := h28) (h35c := h35c) (h218 := h218) (hH := hH) (hcone := hcone) (h23 := h23) (h24c := h24c) (h33 := h33) (hstd := hstd) (hCentre := hCentre) (hOpen := hOpen) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hExist := hExist) (hThm11 := hThm11) (hProp56 := hProp56) (hconf := hconf) (hI2 := hI2) (hK := hK) (hloc := hloc) (hE := hE) (hFL := hFL) (hBG := hBG) (hE1 := hE1) (hE2 := hE2) (hscale := hscale) (hND := hND) (hrescale := hrescale) (hmodel := hmodel) (hcanon := hcanon) (h611 := h611) (h82 := h82) (h0 := h0) (h2 := h2) (hV := hV) (hsup := MatedCRT.frozenLeastSupersolutionMemCone_of_volumeGrowth 𝒮 h27)

end MatedCRT

namespace MatedCRT.FirstPassClosure

open MeasureTheory Set
open _root_.HarmonicBalls

/-- Result 5.1 (`closed_5_1_lp`) with hsup derived from VolumeGrowthStmt (HB Lemma 3.1 deterministic form). -/
theorem closed_5_1_lp_noSup
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (h27 : VolumeGrowthStmt)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{0})
    (h82 : TypicalPointManyGoodScalesStmt.{0})
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hEx : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hSC : ClusterStrongCompatibilityStmt.{0})
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    IDLALowerBoundStmt 𝒮 :=
  MatedCRT.FirstPassClosure.closed_5_1_lp (𝒮 := 𝒮) (ν := ν) (hC := hC) (hmodel := hmodel) (hFL := hFL) (hstd := hstd) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (hscale := hscale) (hND := hND) (hcanon := hcanon) (h32 := h32) (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc) (hSC := hSC) (hBG := hBG) (hsup := MatedCRT.frozenLeastSupersolutionMemCone_of_volumeGrowth 𝒮 h27)

end MatedCRT.FirstPassClosure

namespace MatedCRT.FirstPassClosure

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- Result 5.1 (`closed_5_1_cellRewire`) with hsup derived from VolumeGrowthStmt (HB Lemma 3.1 deterministic form). -/
theorem closed_5_1_cellRewire_noSup
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮)
    (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hG : FrozenGreenDiscPole)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality)
    (hpair : FPPairingLawIG4)
    (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput)
    (h27 : VolumeGrowthStmt)
    (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (hG15 : GreenFunctionCrudeBoundStmt 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{0})
    (h82 : TypicalPointManyGoodScalesStmt.{0})
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hEx : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hSC : ClusterStrongCompatibilityStmt.{0}) :
    IDLALowerBoundStmt 𝒮 :=
  MatedCRT.FirstPassClosure.closed_5_1_cellRewire (𝒮 := 𝒮) (ν := ν) (hC := hC) (hμae := hμae) (hSB := hSB) (hU := hU) (hexc := hexc) (hG := hG) (hmodel := hmodel) (hFL := hFL) (hLoc := hLoc) (hpair := hpair) (hmeasT := hmeasT) (hstd := hstd) (hmin := hmin) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (hscale := hscale) (h27 := h27) (h22 := h22) (h24c := h24c) (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc) (hSC := hSC) (hsup := MatedCRT.frozenLeastSupersolutionMemCone_of_volumeGrowth 𝒮 h27)

end MatedCRT.FirstPassClosure
