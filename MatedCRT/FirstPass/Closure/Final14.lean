import MatedCRT.FirstPass.Closure.AuditRewire14
import MatedCRT.FirstPass.SLERef.CertifiedCore
import MatedCRT.FirstPass.LPBridge.BrownianOutwardExcursion
import MatedCRT.FirstPass.LPBridge.ConeMeanZeroRestrictionFinal

/-!
# Final forms of the convergence results 1.4 and 1.6

Each final theorem is the rewired wrapper of the corresponding audit-stage theorem, with every discharge in one
statement: the certified core, the Brownian outward excursion discharge, the cone mean-zero restriction from the
radial/lateral independence, and the B4 rewire.
-/

namespace MatedCRT
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- **Internal DLA on mated-CRT maps, convergence (1.4), final form.** Built from `MatedCRT.closed_1_4_p3`
(`MatedCRT/FirstPass/Closure/AuditRewire14.lean`), with the following changes. The certified model is replaced by its
core `CertifiedReferenceModelCore ν 𝒮`; its conjunct 17 is supplied by `certifiedReferenceModel_of_core`. The Brownian
outward excursion input is discharged by `frozenBrownianOutwardExcursionAtExit_holds` (for the conversion and for the
binder `hexc`). The cone mean-zero restriction `FPConeMeanZeroRestriction` is discharged by
`fpConeMeanZeroRestriction_holds`, the whole-plane radial/lateral independence `gffRadialLateralIndep_holds` being
proved. The audit B4 variants are rewired to the single input `hrescale`. -/
theorem closed_1_4_final
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
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
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt)
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
   : ConvergenceOfIDLAStmt 𝒮 :=
    closed_1_4_p3 (𝒮 := 𝒮) (ν := ν) (hC := certifiedReferenceModel_of_core hcore MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (hscale := hscale) (hsc := hsc) (hrp := hrp) (hind := hind) (hEnvS := hEnvS) (hm := hm) (hdeg := hdeg) (hBG := hBG) (h28 := h28) (h29 := h29) (h210 := h210) (h214 := h214) (h216 := h216) (h51 := h51) (hH := hH) (h0 := h0) (h2 := h2) (hV := hV) (hR := MatedCRT.ConeMeanZeroRestriction.fpConeMeanZeroRestriction_holds) (hcone := hcone) (hrevuz := hrevuz) (h23 := h23) (hdiv := hdiv) (hF3 := hF3) (hexc := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (hsup := hsup) (hmodel := hmodel) (hFL := hFL) (hstd := hstd) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (h22 := h22) (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc) (hSC := hSC) (hrescale := hrescale)

/-- **Divisible sandpile on mated-CRT maps, convergence (1.6), final form.** Built from `MatedCRT.closed_1_6_p3`
(`MatedCRT/FirstPass/Closure/AuditRewire14.lean`) with the same changes as `closed_1_4_final`: the core
`CertifiedReferenceModelCore` in place of the certified model, the Brownian outward excursion input discharged, the cone
mean-zero restriction discharged by `fpConeMeanZeroRestriction_holds`, and the audit B4 variants rewired to `hrescale`. -/
theorem closed_1_6_final
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
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
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt)
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
   : ConvergenceOfDivSandpileStmt 𝒮 :=
    closed_1_6_p3 (𝒮 := 𝒮) (ν := ν) (hC := certifiedReferenceModel_of_core hcore MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (hscale := hscale) (hsc := hsc) (hrp := hrp) (hind := hind) (hEnvS := hEnvS) (hm := hm) (hdeg := hdeg) (hBG := hBG) (h28 := h28) (h29 := h29) (h210 := h210) (h214 := h214) (h216 := h216) (h51 := h51) (hH := hH) (h0 := h0) (h2 := h2) (hV := hV) (hR := MatedCRT.ConeMeanZeroRestriction.fpConeMeanZeroRestriction_holds) (hcone := hcone) (hrevuz := hrevuz) (h23 := h23) (hdiv := hdiv) (hF3 := hF3) (hexc := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (hsup := hsup) (hmodel := hmodel) (hFL := hFL) (hstd := hstd) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (h22 := h22) (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc) (hSC := hSC) (hrescale := hrescale)

end MatedCRT
