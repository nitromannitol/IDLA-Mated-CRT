import MatedCRT.External.QuantumCone
import MatedCRT.External.SLE
import MatedCRT.FirstPass.Closure.AuditCore
import MatedCRT.FirstPass.Closure.AuditRewire14
import MatedCRT.FirstPass.Closure.Lemma36Rate
import MatedCRT.FirstPass.Closure.Prop51
import MatedCRT.FirstPass.Closure.Prop51Canon
import MatedCRT.FirstPass.Closure.Section3
import MatedCRT.FirstPass.Closure.Theorem14
import MatedCRT.FirstPass.Closure.Theorem14d
import MatedCRT.FirstPass.Frozen.S3S4
import MatedCRT.FirstPass.Frozen.S4d2
import MatedCRT.FirstPass.Frozen.S5BG56
import MatedCRT.FirstPass.Frozen.S5Cited
import MatedCRT.FirstPass.Frozen.S5S6S7
import MatedCRT.FirstPass.HBRewire
import MatedCRT.FirstPass.HdetSwap
import MatedCRT.FirstPass.LPBridge.BrownianOutwardExcursion
import MatedCRT.FirstPass.Main
import MatedCRT.FirstPass.Phase2Rewire
import MatedCRT.FirstPass.S1S2S8SA
import MatedCRT.FirstPass.S2g.HalfBallGate
import MatedCRT.FirstPass.S2j
import MatedCRT.FirstPass.S3S4
import MatedCRT.FirstPass.S3S4b
import MatedCRT.FirstPass.S3i.LensClosed
import MatedCRT.FirstPass.S4d.FixedTimeFinal
import MatedCRT.FirstPass.S4d.HorizonUnique
import MatedCRT.FirstPass.S4d.Provider24
import MatedCRT.FirstPass.S4d.ScaleBridge
import MatedCRT.FirstPass.S4x8
import MatedCRT.FirstPass.S5S6S7
import MatedCRT.FirstPass.S5r.ClosureInside
import MatedCRT.FirstPass.S5u
import MatedCRT.FirstPass.SLERef.Certified
import MatedCRT.FirstPass.SLERef.CertifiedCore
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Proofs.Sec1.ConeScaleRadius
import MatedCRT.Proofs.Sec1.HarmonicBallScaling
import MatedCRT.Proofs.Sec3.ConeBallMass
import MatedCRT.Steps.Sec1.Convergence

/-!
# Closure wrappers with the Brownian outward-excursion input discharged

Each `_bm` theorem is a top-level result of `MatedCRT/FirstPass/Closure/*.lean`, `MatedCRT/FirstPass/Main.lean` or
`MatedCRT/FirstPass/Phase2Rewire.lean` that has a binder of type `FrozenBrownianOutwardExcursionAtExit` or
`BrownianOutwardExcursionAtExitStep`. The wrapper has the same statement without that binder and is proved by the original
applied to `MatedCRT.frozenBrownianOutwardExcursionAtExit_holds` (`MatedCRT/FirstPass/LPBridge/BrownianOutwardExcursion.lean`),
the planar Brownian outward excursion at exit from a disk (strong Markov property at the exit time and Blumenthal 0-1 law;
Mörters-Peres, *Brownian Motion*, Theorems 2.16 and 2.7). The originals are unchanged.

The wrappers are closures of the following numbered results of `paper/idla_mated_crt-corrected.tex`, by label (the
counted forms are listed in docs/campaign/COUNTED.md): Lemma 3.3 (`lemma:uniform-convergence-of-greens-function`), Lemma 3.4
(`lemma:integral-convergence-of-greens-function`), Lemma 3.5 (`lemma:discrete-dirichlet-problem`), Lemma 3.6
(`lemma:convergence-of-harmonic-functions`), Lemma 3.7 (`lemma:convergence-of-the-normalized-exit-time`), Lemma 4.8
(`lemma:subsequential-properties`), Proposition 5.1 (`prop:IDLA-lower-bound`), Theorem 1.4
(`theorem:convergence-of-IDLA`) and Theorem 1.6 (`theorem:convergence-of-div-sandpile`).
-/

namespace MatedCRT
open MeasureTheory

/-- Wrapper of `closed_3_3_hdetSwap_certCore` (`MatedCRT/FirstPass/Closure/AuditCore.lean:26`): the Brownian exit binder(s) `hexit` are removed and discharged by `MatedCRT.frozenBrownianOutwardExcursionAtExit_holds` (unconditional). Same conclusion; the other binders are unchanged. -/
theorem closed_3_3_hdetSwap_certCore_bm
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (h27 : VolumeGrowthStmt)
    (hcl : MatedCRT.TruncatedLaws.BLEnvelopeClosureInput 𝒮)
   :
    UniformConvergenceGreenKernelStmt 𝒮 :=
    closed_3_3_hdetSwap_certCore (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (h27 := h27) (hexit := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (hcl := hcl)
end MatedCRT

namespace MatedCRT
open MeasureTheory

/-- Wrapper of `closed_3_4_certCore` (`MatedCRT/FirstPass/Closure/AuditCore.lean:34`): the Brownian exit binder(s) `hBM` are removed and discharged by `MatedCRT.frozenBrownianOutwardExcursionAtExit_holds` (unconditional). Same conclusion; the other binders are unchanged. -/
theorem closed_3_4_certCore_bm
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (h27 : VolumeGrowthStmt)
   :
    IntegralConvergenceGreenFunctionStmt 𝒮 :=
    closed_3_4_certCore (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hBM := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (h27 := h27)
end MatedCRT

namespace MatedCRT
open MeasureTheory

/-- Wrapper of `closed_3_6_certCore` (`MatedCRT/FirstPass/Closure/AuditCore.lean:42`): the Brownian exit binder(s) `hBM`, `hexc` are removed and discharged by `MatedCRT.frozenBrownianOutwardExcursionAtExit_holds` (unconditional). Same conclusion; the other binders are unchanged. -/
theorem closed_3_6_certCore_bm
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
   :
    ConvergenceHarmonicFunctionsStmt 𝒮 :=
    closed_3_6_certCore (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hBM := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (hexc := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds)
end MatedCRT

namespace MatedCRT
open MeasureTheory

/-- Wrapper of `closed_3_5_certCore` (`MatedCRT/FirstPass/Closure/AuditCore.lean:50`): the Brownian exit binder(s) `hBM`, `hexc` are removed and discharged by `MatedCRT.frozenBrownianOutwardExcursionAtExit_holds` (unconditional). Same conclusion; the other binders are unchanged. -/
theorem closed_3_5_certCore_bm
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (h27 : VolumeGrowthStmt)
   :
    DiscreteDirichletProblemCorrectedStmt 𝒮 :=
    closed_3_5_certCore (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hBM := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (h27 := h27) (hexc := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds)
end MatedCRT

namespace MatedCRT
open MeasureTheory

/-- Wrapper of `closed_3_7_certCore` (`MatedCRT/FirstPass/Closure/AuditCore.lean:58`): the Brownian exit binder(s) `hBM`, `hexc` are removed and discharged by `MatedCRT.frozenBrownianOutwardExcursionAtExit_holds` (unconditional). Same conclusion; the other binders are unchanged. -/
theorem closed_3_7_certCore_bm
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (h27 : VolumeGrowthStmt)
   :
    ConvergenceNormalizedExitTimeStmt 𝒮 :=
    closed_3_7_certCore (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hBM := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (h27 := h27) (hexc := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds)
end MatedCRT

namespace MatedCRT.FirstPassClosure
open MeasureTheory
open _root_.HarmonicBalls

/-- Wrapper of `closed_1_4_wired_certCore` (`MatedCRT/FirstPass/Closure/AuditCore.lean:67`): the Brownian exit binder(s) `hBM`, `hexc` are removed and discharged by `MatedCRT.frozenBrownianOutwardExcursionAtExit_holds` (unconditional). Same conclusion; the other binders are unchanged. -/
theorem closed_1_4_wired_certCore_bm
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
    (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction)
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hcell : FrozenAdjacentCellsMeetAe 𝒮)
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
    (hGBall : _root_.HarmonicBalls.GreenFunctionBallStmt)
    (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple)
    (hpole : FrozenGreenDiscPole)
    (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep)
    (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt)
   :
    ConvergenceOfIDLAStmt 𝒮 :=
    closed_1_4_wired_certCore (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hBM := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (hscale := hscale) (hsc := hsc) (hrp := hrp) (hind := hind) (hEnvS := hEnvS) (hm := hm) (hdeg := hdeg) (h27 := h27) (h28 := h28) (h29 := h29) (h210 := h210) (h214 := h214) (h216 := h216) (h218 := h218) (hH := hH) (h0 := h0) (h2 := h2) (hV := hV) (hR := hR) (hcone := hcone) (hrevuz := hrevuz) (hdet := hdet) (h23 := h23) (hdiv := hdiv) (hF1 := hF1) (hF2 := hF2) (hF3 := hF3) (hcell := hcell) (hexc := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (hμae := hμae) (hSB := hSB) (hsup := hsup) (hmodel := hmodel) (hFL := hFL) (hLoc := hLoc) (hpair := hpair) (hstd := hstd) (hmin := hmin) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (h22 := h22) (h24c := h24c) (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc) (hSC := hSC) (hGBall := hGBall) (hpc := hpc) (hsmp := hsmp) (hpole := hpole) (hnj := hnj) (hcan := hcan) (hcl := hcl) (hcan6 := hcan6)
end MatedCRT.FirstPassClosure

namespace MatedCRT.FirstPassClosure
open MeasureTheory
open _root_.HarmonicBalls

/-- Wrapper of `closed_1_6_wired_certCore` (`MatedCRT/FirstPass/Closure/AuditCore.lean:76`): the Brownian exit binder(s) `hBM`, `hexc` are removed and discharged by `MatedCRT.frozenBrownianOutwardExcursionAtExit_holds` (unconditional). Same conclusion; the other binders are unchanged. -/
theorem closed_1_6_wired_certCore_bm
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
    (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction)
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hcell : FrozenAdjacentCellsMeetAe 𝒮)
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
    (hGBall : _root_.HarmonicBalls.GreenFunctionBallStmt)
    (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple)
    (hpole : FrozenGreenDiscPole)
    (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep)
    (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt)
   :
    ConvergenceOfDivSandpileStmt 𝒮 :=
    closed_1_6_wired_certCore (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hBM := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (hscale := hscale) (hsc := hsc) (hrp := hrp) (hind := hind) (hEnvS := hEnvS) (hm := hm) (hdeg := hdeg) (h27 := h27) (h28 := h28) (h29 := h29) (h210 := h210) (h214 := h214) (h216 := h216) (h218 := h218) (hH := hH) (h0 := h0) (h2 := h2) (hV := hV) (hR := hR) (hcone := hcone) (hrevuz := hrevuz) (hdet := hdet) (h23 := h23) (hdiv := hdiv) (hF1 := hF1) (hF2 := hF2) (hF3 := hF3) (hcell := hcell) (hexc := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (hμae := hμae) (hSB := hSB) (hsup := hsup) (hmodel := hmodel) (hFL := hFL) (hLoc := hLoc) (hpair := hpair) (hstd := hstd) (hmin := hmin) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (h22 := h22) (h24c := h24c) (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc) (hSC := hSC) (hGBall := hGBall) (hpc := hpc) (hsmp := hsmp) (hpole := hpole) (hnj := hnj) (hcan := hcan) (hcl := hcl) (hcan6 := hcan6)
end MatedCRT.FirstPassClosure

namespace MatedCRT.FirstPassClosure
open MeasureTheory
open _root_.HarmonicBalls

/-- Wrapper of `closed_1_4_derived_certCore` (`MatedCRT/FirstPass/Closure/AuditCore.lean:85`): the Brownian exit binder(s) `hBM`, `hexc` are removed and discharged by `MatedCRT.frozenBrownianOutwardExcursionAtExit_holds` (unconditional). Same conclusion; the other binders are unchanged. -/
theorem closed_1_4_derived_certCore_bm
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
    (hR : FPConeMeanZeroRestriction)
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hcell : FrozenAdjacentCellsMeetAe 𝒮)
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
    (hGBall : _root_.HarmonicBalls.GreenFunctionBallStmt)
    (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple)
    (hpole : FrozenGreenDiscPole)
    (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep)
    (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt)
   :
    ConvergenceOfIDLAStmt 𝒮 :=
    closed_1_4_derived_certCore (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hBM := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (hscale := hscale) (hsc := hsc) (hrp := hrp) (hind := hind) (hEnvS := hEnvS) (hm := hm) (hdeg := hdeg) (hBG := hBG) (h28 := h28) (h29 := h29) (h210 := h210) (h214 := h214) (h216 := h216) (h51 := h51) (hH := hH) (h0 := h0) (h2 := h2) (hV := hV) (hR := hR) (hcone := hcone) (hrevuz := hrevuz) (h23 := h23) (hdiv := hdiv) (hF1 := hF1) (hF2 := hF2) (hF3 := hF3) (hcell := hcell) (hexc := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (hμae := hμae) (hSB := hSB) (hsup := hsup) (hmodel := hmodel) (hFL := hFL) (hLoc := hLoc) (hpair := hpair) (hstd := hstd) (hmin := hmin) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (h22 := h22) (h24c := h24c) (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc) (hSC := hSC) (hGBall := hGBall) (hpc := hpc) (hsmp := hsmp) (hpole := hpole) (hnj := hnj) (hcan := hcan) (hcl := hcl) (hcan6 := hcan6)
end MatedCRT.FirstPassClosure

namespace MatedCRT.FirstPassClosure
open MeasureTheory
open _root_.HarmonicBalls

/-- Wrapper of `closed_1_6_derived_certCore` (`MatedCRT/FirstPass/Closure/AuditCore.lean:94`): the Brownian exit binder(s) `hBM`, `hexc` are removed and discharged by `MatedCRT.frozenBrownianOutwardExcursionAtExit_holds` (unconditional). Same conclusion; the other binders are unchanged. -/
theorem closed_1_6_derived_certCore_bm
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
    (hR : FPConeMeanZeroRestriction)
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hcell : FrozenAdjacentCellsMeetAe 𝒮)
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
    (hGBall : _root_.HarmonicBalls.GreenFunctionBallStmt)
    (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple)
    (hpole : FrozenGreenDiscPole)
    (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep)
    (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt)
   :
    ConvergenceOfDivSandpileStmt 𝒮 :=
    closed_1_6_derived_certCore (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hBM := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (hscale := hscale) (hsc := hsc) (hrp := hrp) (hind := hind) (hEnvS := hEnvS) (hm := hm) (hdeg := hdeg) (hBG := hBG) (h28 := h28) (h29 := h29) (h210 := h210) (h214 := h214) (h216 := h216) (h51 := h51) (hH := hH) (h0 := h0) (h2 := h2) (hV := hV) (hR := hR) (hcone := hcone) (hrevuz := hrevuz) (h23 := h23) (hdiv := hdiv) (hF1 := hF1) (hF2 := hF2) (hF3 := hF3) (hcell := hcell) (hexc := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (hμae := hμae) (hSB := hSB) (hsup := hsup) (hmodel := hmodel) (hFL := hFL) (hLoc := hLoc) (hpair := hpair) (hstd := hstd) (hmin := hmin) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (h22 := h22) (h24c := h24c) (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc) (hSC := hSC) (hGBall := hGBall) (hpc := hpc) (hsmp := hsmp) (hpole := hpole) (hnj := hnj) (hcan := hcan) (hcl := hcl) (hcan6 := hcan6)
end MatedCRT.FirstPassClosure

namespace MatedCRT.HBRewire
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls
open MatedCRT.FirstPassClosure

/-- Wrapper of `closed_1_4_derived_hb_certCore` (`MatedCRT/FirstPass/Closure/AuditCore.lean:104`): the Brownian exit binder(s) `hBM`, `hexc` are removed and discharged by `MatedCRT.frozenBrownianOutwardExcursionAtExit_holds` (unconditional). Same conclusion; the other binders are unchanged. -/
theorem closed_1_4_derived_hb_certCore_bm
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
    (hR : FPConeMeanZeroRestriction)
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hcell : FrozenAdjacentCellsMeetAe 𝒮)
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
   :
    ConvergenceOfIDLAStmt 𝒮 :=
    closed_1_4_derived_hb_certCore (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hBM := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (hscale := hscale) (hsc := hsc) (hrp := hrp) (hind := hind) (hEnvS := hEnvS) (hm := hm) (hdeg := hdeg) (hBG := hBG) (h28 := h28) (h29 := h29) (h210 := h210) (h214 := h214) (h216 := h216) (h51 := h51) (hH := hH) (h0 := h0) (h2 := h2) (hV := hV) (hR := hR) (hcone := hcone) (hrevuz := hrevuz) (h23 := h23) (hdiv := hdiv) (hF1 := hF1) (hF2 := hF2) (hF3 := hF3) (hcell := hcell) (hexc := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (hμae := hμae) (hSB := hSB) (hsup := hsup) (hmodel := hmodel) (hFL := hFL) (hLoc := hLoc) (hpair := hpair) (hstd := hstd) (hmin := hmin) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (h22 := h22) (h24c := h24c) (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc) (hSC := hSC) (hpc := hpc) (hsmp := hsmp) (hnj := hnj) (hcan := hcan) (hcl := hcl) (hcan6 := hcan6)
end MatedCRT.HBRewire

namespace MatedCRT.HBRewire
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls
open MatedCRT.FirstPassClosure

/-- Wrapper of `closed_1_6_derived_hb_certCore` (`MatedCRT/FirstPass/Closure/AuditCore.lean:114`): the Brownian exit binder(s) `hBM`, `hexc` are removed and discharged by `MatedCRT.frozenBrownianOutwardExcursionAtExit_holds` (unconditional). Same conclusion; the other binders are unchanged. -/
theorem closed_1_6_derived_hb_certCore_bm
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
    (hR : FPConeMeanZeroRestriction)
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hcell : FrozenAdjacentCellsMeetAe 𝒮)
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
   :
    ConvergenceOfDivSandpileStmt 𝒮 :=
    closed_1_6_derived_hb_certCore (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hBM := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (hscale := hscale) (hsc := hsc) (hrp := hrp) (hind := hind) (hEnvS := hEnvS) (hm := hm) (hdeg := hdeg) (hBG := hBG) (h28 := h28) (h29 := h29) (h210 := h210) (h214 := h214) (h216 := h216) (h51 := h51) (hH := hH) (h0 := h0) (h2 := h2) (hV := hV) (hR := hR) (hcone := hcone) (hrevuz := hrevuz) (h23 := h23) (hdiv := hdiv) (hF1 := hF1) (hF2 := hF2) (hF3 := hF3) (hcell := hcell) (hexc := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (hμae := hμae) (hSB := hSB) (hsup := hsup) (hmodel := hmodel) (hFL := hFL) (hLoc := hLoc) (hpair := hpair) (hstd := hstd) (hmin := hmin) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (h22 := h22) (h24c := h24c) (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc) (hSC := hSC) (hpc := hpc) (hsmp := hsmp) (hnj := hnj) (hcan := hcan) (hcl := hcl) (hcan6 := hcan6)
end MatedCRT.HBRewire

namespace MatedCRT.Phase2
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls
open MatedCRT.FirstPassClosure

/-- Wrapper of `closed_1_4_derived_p2_certCore` (`MatedCRT/FirstPass/Closure/AuditCore.lean:124`): the Brownian exit binder(s) `hBM`, `hexc` are removed and discharged by `MatedCRT.frozenBrownianOutwardExcursionAtExit_holds` (unconditional). Same conclusion; the other binders are unchanged. -/
theorem closed_1_4_derived_p2_certCore_bm
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
    (hR : FPConeMeanZeroRestriction)
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hcell : FrozenAdjacentCellsMeetAe 𝒮)
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
    (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep)
    (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt)
   :
    ConvergenceOfIDLAStmt 𝒮 :=
    closed_1_4_derived_p2_certCore (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hBM := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (hscale := hscale) (hsc := hsc) (hrp := hrp) (hind := hind) (hEnvS := hEnvS) (hm := hm) (hdeg := hdeg) (hBG := hBG) (h28 := h28) (h29 := h29) (h210 := h210) (h214 := h214) (h216 := h216) (h51 := h51) (hH := hH) (h0 := h0) (h2 := h2) (hV := hV) (hR := hR) (hcone := hcone) (hrevuz := hrevuz) (h23 := h23) (hdiv := hdiv) (hF3 := hF3) (hcell := hcell) (hexc := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (hsup := hsup) (hmodel := hmodel) (hFL := hFL) (hstd := hstd) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (h22 := h22) (h24c := h24c) (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc) (hSC := hSC) (hnj := hnj) (hcan := hcan) (hcl := hcl) (hcan6 := hcan6)
end MatedCRT.Phase2

namespace MatedCRT.Phase2
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls
open MatedCRT.FirstPassClosure

/-- Wrapper of `closed_1_6_derived_p2_certCore` (`MatedCRT/FirstPass/Closure/AuditCore.lean:134`): the Brownian exit binder(s) `hBM`, `hexc` are removed and discharged by `MatedCRT.frozenBrownianOutwardExcursionAtExit_holds` (unconditional). Same conclusion; the other binders are unchanged. -/
theorem closed_1_6_derived_p2_certCore_bm
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
    (hR : FPConeMeanZeroRestriction)
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hcell : FrozenAdjacentCellsMeetAe 𝒮)
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
    (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep)
    (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt)
   :
    ConvergenceOfDivSandpileStmt 𝒮 :=
    closed_1_6_derived_p2_certCore (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hBM := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (hscale := hscale) (hsc := hsc) (hrp := hrp) (hind := hind) (hEnvS := hEnvS) (hm := hm) (hdeg := hdeg) (hBG := hBG) (h28 := h28) (h29 := h29) (h210 := h210) (h214 := h214) (h216 := h216) (h51 := h51) (hH := hH) (h0 := h0) (h2 := h2) (hV := hV) (hR := hR) (hcone := hcone) (hrevuz := hrevuz) (h23 := h23) (hdiv := hdiv) (hF3 := hF3) (hcell := hcell) (hexc := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (hsup := hsup) (hmodel := hmodel) (hFL := hFL) (hstd := hstd) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (h22 := h22) (h24c := h24c) (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc) (hSC := hSC) (hnj := hnj) (hcan := hcan) (hcl := hcl) (hcan6 := hcan6)
end MatedCRT.Phase2

namespace MatedCRT
open MeasureTheory

/-- Wrapper of `closed_4_8_corrected_certCore` (`MatedCRT/FirstPass/Closure/AuditCore.lean:142`): the Brownian exit binder(s) `hBM`, `hexc` are removed and discharged by `MatedCRT.frozenBrownianOutwardExcursionAtExit_holds` (unconditional). Same conclusion; the other binders are unchanged. -/
theorem closed_4_8_corrected_certCore_bm
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (h27 : VolumeGrowthStmt)
   :
    SubsequentialPropertiesCorrectedStmt 𝒮 :=
    closed_4_8_corrected_certCore (𝒮 := 𝒮) (ν := ν) (hcore := hcore) (hBM := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (h27 := h27) (hexc := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds)
end MatedCRT

namespace MatedCRT
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls
open MatedCRT.FirstPassClosure

/-- Wrapper of `closed_1_4_p3` (`MatedCRT/FirstPass/Closure/AuditRewire14.lean:53`): the Brownian exit binder(s) `hexc` are removed and discharged by `MatedCRT.frozenBrownianOutwardExcursionAtExit_holds` (unconditional). Same conclusion; the other binders are unchanged. -/
theorem closed_1_4_p3_bm
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
    closed_1_4_p3 (𝒮 := 𝒮) (ν := ν) (hC := hC) (hscale := hscale) (hsc := hsc) (hrp := hrp) (hind := hind) (hEnvS := hEnvS) (hm := hm) (hdeg := hdeg) (hBG := hBG) (h28 := h28) (h29 := h29) (h210 := h210) (h214 := h214) (h216 := h216) (h51 := h51) (hH := hH) (h0 := h0) (h2 := h2) (hV := hV) (hR := hR) (hcone := hcone) (hrevuz := hrevuz) (h23 := h23) (hdiv := hdiv) (hF3 := hF3) (hexc := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (hsup := hsup) (hmodel := hmodel) (hFL := hFL) (hstd := hstd) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (h22 := h22) (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc) (hSC := hSC) (hrescale := hrescale)
end MatedCRT

namespace MatedCRT
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls
open MatedCRT.FirstPassClosure

/-- Wrapper of `closed_1_6_p3` (`MatedCRT/FirstPass/Closure/AuditRewire14.lean:143`): the Brownian exit binder(s) `hexc` are removed and discharged by `MatedCRT.frozenBrownianOutwardExcursionAtExit_holds` (unconditional). Same conclusion; the other binders are unchanged. -/
theorem closed_1_6_p3_bm
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
    closed_1_6_p3 (𝒮 := 𝒮) (ν := ν) (hC := hC) (hscale := hscale) (hsc := hsc) (hrp := hrp) (hind := hind) (hEnvS := hEnvS) (hm := hm) (hdeg := hdeg) (hBG := hBG) (h28 := h28) (h29 := h29) (h210 := h210) (h214 := h214) (h216 := h216) (h51 := h51) (hH := hH) (h0 := h0) (h2 := h2) (hV := hV) (hR := hR) (hcone := hcone) (hrevuz := hrevuz) (h23 := h23) (hdiv := hdiv) (hF3 := hF3) (hexc := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (hsup := hsup) (hmodel := hmodel) (hFL := hFL) (hstd := hstd) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (h22 := h22) (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc) (hSC := hSC) (hrescale := hrescale)
end MatedCRT

namespace MatedCRT
open MeasureTheory

/-- Wrapper of `closed_3_6_rate` (`MatedCRT/FirstPass/Closure/Lemma36Rate.lean:30`): the Brownian exit binder(s) `hexc` are removed and discharged by `MatedCRT.frozenBrownianOutwardExcursionAtExit_holds` (unconditional). Same conclusion; the other binders are unchanged. -/
theorem closed_3_6_rate_bm
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hBE : MatedCRT.FirstPass36.FrozenOneSidedBoundaryContinuity 𝒮)
   :
    MatedCRT.FirstPass36.CorrectedHarmonicSameWalkAnnealedStmt 𝒮 :=
    closed_3_6_rate (𝒮 := 𝒮) (ν := ν) (hC := hC) (hexc := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (hBE := hBE)
end MatedCRT

namespace MatedCRT
open MeasureTheory

/-- Wrapper of `closed_3_6_full` (`MatedCRT/FirstPass/Closure/Lemma36Rate.lean:39`): the Brownian exit binder(s) `hexc` are removed and discharged by `MatedCRT.frozenBrownianOutwardExcursionAtExit_holds` (unconditional). Same conclusion; the other binders are unchanged. -/
theorem closed_3_6_full_bm
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hBE : MatedCRT.FirstPass36.FrozenOneSidedBoundaryContinuity 𝒮)
   :
    CorrectedHarmonicConvergenceStmt 𝒮 ∧ MatedCRT.FirstPass36.CorrectedHarmonicSameWalkAnnealedStmt 𝒮 :=
    closed_3_6_full (𝒮 := 𝒮) (ν := ν) (hC := hC) (hexc := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (hBE := hBE)
end MatedCRT

namespace MatedCRT.FirstPassClosure
open MeasureTheory Filter Topology Set Metric
open _root_.HarmonicBalls

/-- Wrapper of `closed_5_1_canon_noCell` (`MatedCRT/FirstPass/Closure/Prop51Canon.lean:70`): the Brownian exit binder(s) `hexc` are removed and discharged by `MatedCRT.frozenBrownianOutwardExcursionAtExit_holds` (unconditional). Same conclusion; the other binders are unchanged. -/
theorem closed_5_1_canon_noCell_bm
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮)
    (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮)
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
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
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
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
   :
    IDLALowerBoundStmt 𝒮 :=
    closed_5_1_canon_noCell (𝒮 := 𝒮) (ν := ν) (hC := hC) (hμae := hμae) (hSB := hSB) (hsup := hsup) (hU := hU) (hexc := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (hG := hG) (hmodel := hmodel) (hFL := hFL) (hLoc := hLoc) (hpair := hpair) (hmeasT := hmeasT) (hstd := hstd) (hmin := hmin) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (hscale := hscale) (h27 := h27) (h22 := h22) (h24c := h24c) (hcanon := hcanon) (h32 := h32) (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc) (hSC := hSC)
end MatedCRT.FirstPassClosure

namespace MatedCRT

/-- Wrapper of `firstPassMain_1_4` (`MatedCRT/FirstPass/Main.lean:46`): the Brownian exit binder(s) `hexc` are removed and discharged by `MatedCRT.frozenBrownianOutwardExcursionAtExit_holds` (unconditional). Same conclusion; the other binders are unchanged. -/
theorem firstPassMain_1_4_bm
    (𝒮 : SpaceFillingSLEModel)
    (hscale : QuantumConeScalingInput)
    (hm : MepsScalingInput 𝒮)
    (hdeg : DegreeBoundInput 𝒮)
    (h22 : LQGMeasurePropertiesStmt)
    (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (hEnv : FrozenConeEnvironmentScaling 𝒮)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction)
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (h25 : ConeScaleInvarianceUpToFixedTimeStmt)
    (h211 : RandomWalkToLBMStmt 𝒮)
    (hrevuz : FrozenLBMGreenOccupation 𝒮)
    (hdet : FrozenTruncatedDetFixedTime 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h42 : DivSandpileLowerBoundStmt 𝒮)
    (h51 : IDLALowerBoundStmt 𝒮)
    (h61 : IDLAUpperBoundStmt 𝒮)
    (hT : ScaledClusterExitTimeStep)
   :
    ConvergenceOfIDLAStmt 𝒮 :=
    firstPassMain_1_4 (𝒮 := 𝒮) (hscale := hscale) (hm := hm) (hdeg := hdeg) (h22 := h22) (h27 := h27) (h28 := h28) (h29 := h29) (h210 := h210) (h214 := h214) (h216 := h216) (h218 := h218) (hH := hH) (hEnv := hEnv) (h0 := h0) (h2 := h2) (hV := hV) (hR := hR) (h24 := h24) (h25 := h25) (h211 := h211) (hrevuz := hrevuz) (hdet := hdet) (hexc := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (h35 := h35) (h42 := h42) (h51 := h51) (h61 := h61) (hT := hT)
end MatedCRT

namespace MatedCRT

/-- Wrapper of `firstPassMain_1_6` (`MatedCRT/FirstPass/Main.lean:74`): the Brownian exit binder(s) `hexc` are removed and discharged by `MatedCRT.frozenBrownianOutwardExcursionAtExit_holds` (unconditional). Same conclusion; the other binders are unchanged. -/
theorem firstPassMain_1_6_bm
    (𝒮 : SpaceFillingSLEModel)
    (hscale : QuantumConeScalingInput)
    (hm : MepsScalingInput 𝒮)
    (hdeg : DegreeBoundInput 𝒮)
    (h22 : LQGMeasurePropertiesStmt)
    (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (hEnv : FrozenConeEnvironmentScaling 𝒮)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction)
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (h25 : ConeScaleInvarianceUpToFixedTimeStmt)
    (h211 : RandomWalkToLBMStmt 𝒮)
    (hrevuz : FrozenLBMGreenOccupation 𝒮)
    (hdet : FrozenTruncatedDetFixedTime 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h42 : DivSandpileLowerBoundStmt 𝒮)
    (h51 : IDLALowerBoundStmt 𝒮)
    (h61 : IDLAUpperBoundStmt 𝒮)
    (hT : ScaledClusterExitTimeStep)
   :
    ConvergenceOfDivSandpileStmt 𝒮 :=
    firstPassMain_1_6 (𝒮 := 𝒮) (hscale := hscale) (hm := hm) (hdeg := hdeg) (h22 := h22) (h27 := h27) (h28 := h28) (h29 := h29) (h210 := h210) (h214 := h214) (h216 := h216) (h218 := h218) (hH := hH) (hEnv := hEnv) (h0 := h0) (h2 := h2) (hV := hV) (hR := hR) (h24 := h24) (h25 := h25) (h211 := h211) (hrevuz := hrevuz) (hdet := hdet) (hexc := MatedCRT.frozenBrownianOutwardExcursionAtExit_holds) (h35 := h35) (h42 := h42) (h51 := h51) (h61 := h61) (hT := hT)
end MatedCRT

#print axioms MatedCRT.closed_3_3_hdetSwap_certCore_bm
#print axioms MatedCRT.closed_3_4_certCore_bm
#print axioms MatedCRT.closed_3_6_certCore_bm
#print axioms MatedCRT.closed_3_5_certCore_bm
#print axioms MatedCRT.closed_3_7_certCore_bm
#print axioms MatedCRT.FirstPassClosure.closed_1_4_wired_certCore_bm
#print axioms MatedCRT.FirstPassClosure.closed_1_6_wired_certCore_bm
#print axioms MatedCRT.FirstPassClosure.closed_1_4_derived_certCore_bm
#print axioms MatedCRT.FirstPassClosure.closed_1_6_derived_certCore_bm
#print axioms MatedCRT.HBRewire.closed_1_4_derived_hb_certCore_bm
#print axioms MatedCRT.HBRewire.closed_1_6_derived_hb_certCore_bm
#print axioms MatedCRT.Phase2.closed_1_4_derived_p2_certCore_bm
#print axioms MatedCRT.Phase2.closed_1_6_derived_p2_certCore_bm
#print axioms MatedCRT.closed_4_8_corrected_certCore_bm
#print axioms MatedCRT.closed_1_4_p3_bm
#print axioms MatedCRT.closed_1_6_p3_bm
#print axioms MatedCRT.closed_3_6_rate_bm
#print axioms MatedCRT.closed_3_6_full_bm
#print axioms MatedCRT.FirstPassClosure.closed_5_1_canon_noCell_bm
#print axioms MatedCRT.firstPassMain_1_4_bm
#print axioms MatedCRT.firstPassMain_1_6_bm
