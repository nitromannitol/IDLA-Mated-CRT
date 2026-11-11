import MatedCRT.FirstPass.Closure.Final14
import MatedCRT.FirstPass.SLERef.CertifiedCore
import MatedCRT.FirstPass.SLERef.Certified
import MatedCRT.FirstPass.S5qe
import MatedCRT.FirstPass.LPBridge.BrownianOutwardExcursion

/-!
# Final forms of the convergence results 1.4 and 1.6, with the discharged binders

`closed_1_4_composed` and `closed_1_6_composed` are the final theorems `closed_1_4_final` and `closed_1_6_final`
(`MatedCRT/FirstPass/Closure/Final14.lean`) with eleven of their hypotheses discharged by projections of the certified
reference model. The projections are the accessors `CertifiedReferenceModelCore.*` (`MatedCRT/FirstPass/S5qe.lean`) and
`CertifiedReferenceModel.*` (`MatedCRT/FirstPass/SLERef/Certified.lean`), the latter applied to
`certifiedReferenceModel_of_core hcore frozenBrownianOutwardExcursionAtExit_holds`. No new hypothesis is introduced.
The hypothesis `hcore : CertifiedReferenceModelCore ν 𝒮` is a conjunction that contains the discharged Props.
-/

namespace MatedCRT
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- **Internal DLA on mated-CRT maps, convergence (1.4), with the projected hypotheses discharged.** The conclusion is
`ConvergenceOfIDLAStmt 𝒮`, as for `closed_1_4_final`. The discharged binders are `h28`, `h29`, `h210`, `h214`, `h216`
(Draft statements of the cell size, counting measure, degree measure and Green kernel bounds), `h51` (BG20 Proposition
5.1), `hm` (scaling of the expected exit time), `hdeg` (degree bound), `hcone` (cone scaling law), `hrevuz` (occupation
measure of the Green kernel) and `hH` (discrete Hölder continuity). -/
theorem closed_1_4_composed
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
  MatedCRT.closed_1_4_final (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hscale := hscale) (hsc := hsc) (hrp := hrp) (hind := hind) (hEnvS := hEnvS) (hm := MatedCRT.CertifiedReferenceModelCore.mepsScaling hcore) (hdeg := MatedCRT.CertifiedReferenceModel.degreeBound (MatedCRT.certifiedReferenceModel_of_core hcore MatedCRT.frozenBrownianOutwardExcursionAtExit_holds)) (hBG := hBG) (h28 := MatedCRT.CertifiedReferenceModelCore.cellSizeEstimate hcore) (h29 := MatedCRT.CertifiedReferenceModel.countingMeasureConvergence (MatedCRT.certifiedReferenceModel_of_core hcore MatedCRT.frozenBrownianOutwardExcursionAtExit_holds)) (h210 := MatedCRT.CertifiedReferenceModelCore.degreeMeasureConvergence hcore) (h214 := MatedCRT.CertifiedReferenceModelCore.greenKernelUpperBound hcore) (h216 := MatedCRT.CertifiedReferenceModelCore.greenKernelLowerBound hcore) (h51 := MatedCRT.CertifiedReferenceModel.bg20Prop51 (MatedCRT.certifiedReferenceModel_of_core hcore MatedCRT.frozenBrownianOutwardExcursionAtExit_holds)) (hH := MatedCRT.CertifiedReferenceModelCore.frozenDiscreteHolderContinuityCorrected hcore) (h0 := h0) (h2 := h2) (hV := hV) (hcone := MatedCRT.CertifiedReferenceModelCore.frozenConeScaling hcore) (hrevuz := MatedCRT.CertifiedReferenceModelCore.frozenLBMGreenOccupation hcore) (h23 := h23) (hdiv := hdiv) (hF3 := hF3) (hsup := hsup) (hmodel := hmodel) (hFL := hFL) (hstd := hstd) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (h22 := h22) (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc) (hSC := hSC) (hrescale := hrescale)

/-- **Divisible sandpile on mated-CRT maps, convergence (1.6), with the projected hypotheses discharged.** The conclusion
is `ConvergenceOfDivSandpileStmt 𝒮`, as for `closed_1_6_final`, with the same discharged binders as
`closed_1_4_composed`. -/
theorem closed_1_6_composed
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
  MatedCRT.closed_1_6_final (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hscale := hscale) (hsc := hsc) (hrp := hrp) (hind := hind) (hEnvS := hEnvS) (hm := MatedCRT.CertifiedReferenceModelCore.mepsScaling hcore) (hdeg := MatedCRT.CertifiedReferenceModel.degreeBound (MatedCRT.certifiedReferenceModel_of_core hcore MatedCRT.frozenBrownianOutwardExcursionAtExit_holds)) (hBG := hBG) (h28 := MatedCRT.CertifiedReferenceModelCore.cellSizeEstimate hcore) (h29 := MatedCRT.CertifiedReferenceModel.countingMeasureConvergence (MatedCRT.certifiedReferenceModel_of_core hcore MatedCRT.frozenBrownianOutwardExcursionAtExit_holds)) (h210 := MatedCRT.CertifiedReferenceModelCore.degreeMeasureConvergence hcore) (h214 := MatedCRT.CertifiedReferenceModelCore.greenKernelUpperBound hcore) (h216 := MatedCRT.CertifiedReferenceModelCore.greenKernelLowerBound hcore) (h51 := MatedCRT.CertifiedReferenceModel.bg20Prop51 (MatedCRT.certifiedReferenceModel_of_core hcore MatedCRT.frozenBrownianOutwardExcursionAtExit_holds)) (hH := MatedCRT.CertifiedReferenceModelCore.frozenDiscreteHolderContinuityCorrected hcore) (h0 := h0) (h2 := h2) (hV := hV) (hcone := MatedCRT.CertifiedReferenceModelCore.frozenConeScaling hcore) (hrevuz := MatedCRT.CertifiedReferenceModelCore.frozenLBMGreenOccupation hcore) (h23 := h23) (hdiv := hdiv) (hF3 := hF3) (hsup := hsup) (hmodel := hmodel) (hFL := hFL) (hstd := hstd) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (h22 := h22) (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc) (hSC := hSC) (hrescale := hrescale)

end MatedCRT
