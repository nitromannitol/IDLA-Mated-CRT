import HarmonicBalls.Assembly.ExistenceUniqueness
import HarmonicBalls.FirstPass.S2S3S4S9SA
import HarmonicBalls.Proofs.Sec3.Basic
import HarmonicBalls.Proofs.Sec3.ClusterCompatibility
import HarmonicBalls.Proofs.Sec3.ConservationOfMassLemma
import HarmonicBalls.Proofs.Sec3.OpenLaplacian
import MatedCRT.Assembly.Main
import MatedCRT.Audit.StatementsSec3Sec5M1
import MatedCRT.FirstPass.Closure.OwnBinderRewire
import MatedCRT.FirstPass.Closure.Section4
import MatedCRT.FirstPass.Closure.Steps42
import MatedCRT.FirstPass.Derived.ConeCircleLawUnique
import MatedCRT.FirstPass.Derived.ConeWholePlaneFieldLaw
import MatedCRT.FirstPass.Derived.Counted
import MatedCRT.FirstPass.Derived.DiscGreenCentre
import MatedCRT.FirstPass.Derived.HarmonicBallsVolumeGrowth
import MatedCRT.FirstPass.Derived.InsertionCoordinateRule
import MatedCRT.FirstPass.Derived.LQGMeasureInputs
import MatedCRT.FirstPass.HBRewire
import MatedCRT.FirstPass.LIClosed68Y
import MatedCRT.FirstPass.LPBridge.ConeMeanZeroRestrictionFinal
import MatedCRT.FirstPass.LPBridge.LQGTestIntegralMeasurable
import MatedCRT.FirstPass.LPBridge.MinimumPrinciples
import MatedCRT.FirstPass.LPBridge.PunctureConnected
import MatedCRT.FirstPass.LPBridge.UniversalMeasurability
import MatedCRT.FirstPass.S2g.Draft24
import MatedCRT.FirstPass.S2g.HalfBallGate
import MatedCRT.FirstPass.S2y.ConeCircleAbsApprox
import MatedCRT.FirstPass.S2y.LateralAssembly250
import MatedCRT.FirstPass.S3g
import MatedCRT.FirstPass.S4S6c.CGRCYSqInst68
import MatedCRT.FirstPass.S4S6c.CountingExitAlpha68
import MatedCRT.FirstPass.S4S6c.ShellChainCGRCY68
import MatedCRT.FirstPass.S4S6c.ShellChainCGRCYSq68
import MatedCRT.FirstPass.S4S6c.ShellChainCGRCYSqHalf68
import MatedCRT.FirstPass.S4S6c.Uniform68Final
import MatedCRT.FirstPass.S4d.DeterministicComparison
import MatedCRT.FirstPass.S4d.HorizonUnique
import MatedCRT.FirstPass.S4d.ScaleBridge
import MatedCRT.FirstPass.S4d.StrictGapReduction
import MatedCRT.FirstPass.S6d
import MatedCRT.FirstPass.S6q
import MatedCRT.FirstPass.S6r.ShortWindow
import MatedCRT.FirstPass.S6r.ShortWindowClosed
import MatedCRT.FirstPass.S6r.ShortWindowHV
import MatedCRT.FirstPass.SLERef.Certified
import MatedCRT.Proofs.Measurability.ConvergenceDivisibleEvent
import MatedCRT.Proofs.Sec1.ConeScaleRadius
import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.RadialContainment
import MatedCRT.Proofs.Sec2.LQGMeasureProperties.Main
import MatedCRT.Proofs.Sec2.LQGMeasureProperties.NonAtomicScaling
import MatedCRT.Proofs.Sec3.ConeBallMass
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.AlmostSureInterior
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.MaximumPrinciple
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.PreparedProperties
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.Final
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.OdometerComparisonProved
import MatedCRT.Proofs.Sec4.ObstacleSpecialization.Final
import MatedCRT.Proofs.Sec4.SubsequentialProperties.PreparedIdentification

/-!
# Counted theorems from the hypotheses their conclusions need

For each counted theorem of the paper (in its form with derivable inputs supplied, when it has one) whose
conclusion follows from a proper subset of its hypotheses by theorems of this repository and of the
Harmonic-Balls package, the theorem `<name>_minimalInputs` states the conclusion from that subset. No binder
is added; the counted theorems and the frozen statements are unchanged. Each `have` line is one theorem
applied to remaining binders and to earlier lines.

This file is generated from the signatures of the counted theorems; do not edit by hand.
-/

namespace MatedCRT.FirstPassClosure

open MeasureTheory Set
open _root_.HarmonicBalls

/-- The conclusion of `MatedCRT.FirstPassClosure.closed_4_2_lp_derivedInputs` (MatedCRT/FirstPass/Derived/Counted.lean) from its hypotheses without `hcone`: it is not needed. The remaining binders are copied unchanged. -/
theorem closed_4_2_lp_minimalInputs
    {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮)
    (h35c : DiscreteDirichletProblemCorrectedStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hrescale : ConeRescaledMeasureIsConeFieldInput) :
    DivSandpileLowerBoundStmt 𝒮 :=
  have d1 := HarmonicBalls.firstPass_2_3
  have d2 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d3 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d5 := MatedCRT.HBRewire.FrozenGreenDiscPole_of_hb
  have d6 := MatedCRT.coneCircleAverageLocalityStep_proved
  have d7 := MatedCRT.coneCircleLawUniqueStep_holds
  have d8 := MatedCRT.fpStrongMinimumPrinciple_holds
  have d9 := MatedCRT.frozenGreenBallCentre_holds
  have d10 := MatedCRT.frozenLQGTestIntegralMeasurable_holds
  have d11 := MatedCRT.frozenPunctureConnected_holds
  have d12 := MatedCRT.frozenSuperharmonicMinimumPrinciple_holds
  have d13 := MatedCRT.frozenUniversalMeasurabilityOfAnalytic_holds
  have d14 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d15 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d16 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d17 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d18 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d19 := MatedCRT.LQGMeasure.coneFieldScalingStep_proved_radial (hscale := hscale)
  have d20 := MatedCRT.LQGMeasure.lqgMeasureDilationCovariancePart_of_nonDyadic (hND := hND)
  have d21 := MatedCRT.MainHypotheses.maximumPrinciple (𝒮 := 𝒮)
  have d22 := MatedCRT.closed_4_4
  have d23 := MatedCRT.coneScaleRadiusPosStep_of_input (hscale := hscale)
  have d24 := MatedCRT.firstPass_2_17_ownBinders (hBG := hBG)
  have d25 := MatedCRT.obstacleLimitUniqueness (𝒮 := 𝒮)
  have d26 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d27 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d28 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d26)
  have d29 := MatedCRT.LQGMeasure.coneLQGScalingStep_of_dilation (hIV := d20) (hpos := d23)
  have d30 := MatedCRT.FirstPass35Bridge.discreteDirichletProblem_of_corrected_of_steps (h28 := h28) (h35c := h35c)
  have d31 := MatedCRT.LQGMeasure.lqgMeasureNonAtomicPart_of_scaling (h27 := d27) (hfield := d19) (hlqg := d29)
  have d32 := MatedCRT.LQGMeasure.lqgMeasureProperties_of_citedInputs (hNA := d31) (hCL := d6) (hND := hND)
  have d33 := MatedCRT.equibounded_of_boundedExitTime (h217 := d24) (h218 := h218) (hm := hm)
  have d34 := MatedCRT.discretePotentialTightnessAeStep_of_inputs (hm := hm) (h217 := d24) (h218 := h218) (hH := hH)
  have d35 := MatedCRT.strictGapDeterministicComparison_of_frozen (hG := d1) (hpc := d11) (hsmp := d8) (hwmp := d12)
    (hpole := d5)
  have d36 := MatedCRT.Audit.StatementsSec3Sec5M1.three_three_final_reduction (𝒮 := 𝒮) (h210 := h210) (h34 := h34)
    (h214 := h214) (h28 := h28) (hAe := d34)
  have d37 := MatedCRT.FirstPassClosure.coneHalfBallClosureInsideStep_proof (hI2 := hI2) (hK := d3) (hloc := hloc)
    (hEx := hExist) (hE := d4) (hFL := d2) (hBG := hBG)
  have d38 := MatedCRT.closed_2_5_lp_derivedInputs (hstd := hstd) (hBdry := hBdry) (hExist := hExist) (hconf := hconf)
    (hI2 := hI2) (hloc := hloc) (hBG := hBG) (hE2 := hE2) (hscale := hscale) (hND := hND)
  have d39 := MatedCRT.subsequentialPropertiesPrepared_of_identified_estimates (𝒮 := 𝒮) (hm := hm) (h47 := d33)
    (h44 := d22) (h33 := d36) (h35 := d30) (h218 := h218) (hH := hH) (h217 := d24) (h27 := d27)
  have d40 := MatedCRT.closed_2_3_lp_derivedInputs (hBG := hBG) (hscale := hscale) (hND := hND) (hstd := hstd)
    (hBdryHB := hBdry) (hExistHB := hExist) (hconf := hconf) (hI2HB := hI2) (hlocHB := hloc) (hE2 := hE2)
    (hrescale := hrescale)
  have d41 := MatedCRT.coneCanonicalHalfBallStep_of_draft (hU := d13) (hmeasT := d10) (hstd := hstd) (hmin := d12)
    (hC := d9) (hGB := d1) (hpole := d5) (hOpen := d17) (hSup := d18) (hCons := d15) (hMono := d16) (hCompat := d14)
    (hBdry := hBdry) (hExist := hExist) (hThm11 := d28) (hProp56 := d26) (hconf := hconf)
  have d42 := MatedCRT.FirstPassClosure.strictGapFixedTimeUnionStep_proof_unconditional (hstd := hstd) (hCentre := d9)
    (hOpen := d17) (hSup := d18) (hCons := d15) (hMono := d16) (hCompat := d14) (hBdry := hBdry) (hExist := hExist)
    (hThm11 := d28) (hProp56 := d26) (hconf := hconf) (hI2 := hI2) (hK := d3) (hloc := hloc) (hE := d4) (hFL := d2)
    (hBG := hBG) (hE1 := d7) (hE2 := hE2) (hscale := hscale) (hND := hND) (hrescale := hrescale)
  have d43 := MatedCRT.coneHarmonicBallsUpToFixedTimeStmt_of_canonical (hcan := d41) (hcl := d37)
  have d44 := MatedCRT.coneRescaledHalfBallHorizonUnique_fp (hcan := d41) (hcl := d37) (hrescale := hrescale)
  have d45 := MatedCRT.harmonicBallStrictObstacleGapStep_of_steps (𝒮 := 𝒮) (hdet := d35) (hnj := d42)
  have d46 := MatedCRT.coneScaleInvarianceUpToFixedTimeStmt_of_canonical (hcan := d41) (hcl := d37) (hc25 := d38)
    (hU := d44)
  have d47 := MatedCRT.coneFamilyAEMeasurableStep_of_numbered_results (h24 := d43) (h25 := d46) (h27 := d27)
    (hscale := hscale) (h22 := d32)
  have d48 := MatedCRT.obstacleClusterInnerApproximation_of_strictGap (𝒮 := 𝒮) (h27 := d27) (hfam := d47) (h24 := d43)
    (hgap := d45)
  have d49 := MatedCRT.convergenceDivisibleEventMeasurableStep_of_coneFamilyAEMeasurable (𝒮 := 𝒮) (h27 := d27)
    (hfam := d47) (h24 := d43)
  have d50 := MatedCRT.convergenceDivisible_of_prepared_properties (𝒮 := 𝒮) (h48 := d39) (hu := d25) (hm := d49)
  MatedCRT.divSandpileLowerBound_of_inputs (𝒮 := 𝒮) (h41 := d50) (h23 := d40) (h213 := d21) (h33 := d36) (h28 := h28)
    (happrox := d48)

end MatedCRT.FirstPassClosure

namespace MatedCRT.LIClosed68Y

open MeasureTheory

/-- The conclusion of `MatedCRT.LIClosed68Y.firstPass_6_7_derivedInputs` (MatedCRT/FirstPass/Derived/Counted.lean) from its hypotheses without `hLit`, `hμ`: they are not needed. The remaining binders are copied unchanged. -/
theorem firstPass_6_7_minimalInputs
    {ν : ℝ → Measure SLEPathCode}
    {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange)
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    FaithfulConstantOrderLowerBoundStmt 𝒮 :=
  have d1 := MatedCRT.ConeMeanZeroRestriction.fpConeMeanZeroRestriction_holds
  have d2 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d3 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  have d4 := MatedCRT.Lemma68Window.shortWindow_hL_proved
  have d5 := MatedCRT.Lemma68CGRCYSqInst.shellOneTestOrderAeCGRCYSq_holds (𝒮 := 𝒮)
  have d6 := MatedCRT.Lemma68Window.shortWindow_hT_of_meanZero (hR := d1)
  have d7 := MatedCRT.LIClosed68Y.fieldVolCutoffStmt_of_berestyckiGwynne (𝒮 := 𝒮) (hBG := hBG)
  have d8 := MatedCRT.ShortWindowHV.wholePlaneUpperVolumeTailStep_of_ballMass (hBM := hBM) (hCC := hCC)
  have d9 := MatedCRT.CertifiedReferenceModel.cellSizeEstimate (h := hCRM)
  have d10 := MatedCRT.CertifiedReferenceModel.countingMeasureConvergence (h := hCRM)
  have d11 := MatedCRT.CertifiedReferenceModel.exitTimeUpperBound (h := hCRM)
  have d12 := MatedCRT.CertifiedReferenceModel.greenKernelLowerBound (h := hCRM)
  have d13 := MatedCRT.CountingExitAlpha68.countingAtExitAlphaStmt_of_counting_exit (hC := d10) (hE := d11)
  have d14 := MatedCRT.FirstPass64.firstPass_6_5_uniform (h0 := d3) (h2 := d2) (hV := d8)
  have d15 := MatedCRT.Lemma68Window.shortWindow_prevalence (h65 := d14) (hT := d6) (hL := d4)
  have d16 := MatedCRT.Lemma68CGRCY.countingMeshEventsHi_of_draft (𝒮 := 𝒮) (hG := d12) (hC := d9) (hK := d13)
  have d17 := MatedCRT.Lemma68CGRCYSq.shellChainCGRCYSq_of_oneTestOrderCGRCYSq (hprev := d15) (h := d5)
  have d18 := MatedCRT.Lemma68CGRCYSqHalf.guardProbStmtCGRCYSq_of_chain (𝒮 := 𝒮) (hMesh := d16) (hVol := d7)
    (hChain := d17)
  have d19 := MatedCRT.uniformConstantOrderLowerBound_of_guard (𝒮 := 𝒮) (hG := d18)
  MatedCRT.firstPass_6_7_faithful (𝒮 := 𝒮) (hU := d19)

end MatedCRT.LIClosed68Y

namespace MatedCRT.LIClosed68Y

open MeasureTheory

/-- The conclusion of `MatedCRT.LIClosed68Y.firstPass_6_8_derivedInputs` (MatedCRT/FirstPass/Derived/Counted.lean) from its hypotheses without `hLit`, `hμ`: they are not needed. The remaining binders are copied unchanged. -/
theorem firstPass_6_8_minimalInputs
    {ν : ℝ → Measure SLEPathCode}
    {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange)
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    FaithfulConstantOrderLowerBoundDivStmt 𝒮 :=
  have d1 := MatedCRT.ConeMeanZeroRestriction.fpConeMeanZeroRestriction_holds
  have d2 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d3 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  have d4 := MatedCRT.Lemma68Window.shortWindow_hL_proved
  have d5 := MatedCRT.Lemma68CGRCYSqInst.shellOneTestOrderAeCGRCYSq_holds (𝒮 := 𝒮)
  have d6 := MatedCRT.Lemma68Window.shortWindow_hT_of_meanZero (hR := d1)
  have d7 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d8 := MatedCRT.LIClosed68Y.fieldVolCutoffStmt_of_berestyckiGwynne (𝒮 := 𝒮) (hBG := hBG)
  have d9 := MatedCRT.ShortWindowHV.wholePlaneUpperVolumeTailStep_of_ballMass (hBM := hBM) (hCC := hCC)
  have d10 := MatedCRT.CertifiedReferenceModel.cellSizeEstimate (h := hCRM)
  have d11 := MatedCRT.CertifiedReferenceModel.countingMeasureConvergence (h := hCRM)
  have d12 := MatedCRT.CertifiedReferenceModel.exitTimeUpperBound (h := hCRM)
  have d13 := MatedCRT.CertifiedReferenceModel.greenKernelLowerBound (h := hCRM)
  have d14 := MatedCRT.CountingExitAlpha68.countingAtExitAlphaStmt_of_counting_exit (hC := d11) (hE := d12)
  have d15 := MatedCRT.FirstPass64.firstPass_6_5_uniform (h0 := d3) (h2 := d2) (hV := d9)
  have d16 := MatedCRT.Lemma68Window.shortWindow_prevalence (h65 := d15) (hT := d6) (hL := d4)
  have d17 := MatedCRT.Lemma68CGRCY.countingMeshEventsHi_of_draft (𝒮 := 𝒮) (hG := d13) (hC := d10) (hK := d14)
  have d18 := MatedCRT.Lemma68CGRCYSq.shellChainCGRCYSq_of_oneTestOrderCGRCYSq (hprev := d16) (h := d5)
  have d19 := MatedCRT.Lemma68CGRCYSqHalf.guardProbStmtCGRCYSq_of_chain (𝒮 := 𝒮) (hMesh := d17) (hVol := d8)
    (hChain := d18)
  have d20 := MatedCRT.uniformConstantOrderLowerBound_of_guard (𝒮 := 𝒮) (hG := d19)
  MatedCRT.firstPass_6_8_faithful (𝒮 := 𝒮) (hU := d20) (h27 := d7) (h28 := d10)

end MatedCRT.LIClosed68Y

namespace MatedCRT.LIClosed68Y

open MeasureTheory

/-- The conclusion of `MatedCRT.LIClosed68Y.firstPass_6_9_derivedInputs` (MatedCRT/FirstPass/Derived/Counted.lean) from its hypotheses without `hLit`, `hμ`: they are not needed. The remaining binders are copied unchanged. -/
theorem firstPass_6_9_minimalInputs
    {ν : ℝ → Measure SLEPathCode}
    {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange)
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    FaithfulChanceOfBeingAbsorbedStmt 𝒮 :=
  have d1 := MatedCRT.ConeMeanZeroRestriction.fpConeMeanZeroRestriction_holds
  have d2 := MatedCRT.FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
  have d3 := MatedCRT.FirstPass.Derived.wholePlaneLQGExistenceStep_holds
  have d4 := MatedCRT.Lemma68Window.shortWindow_hL_proved
  have d5 := MatedCRT.Lemma68CGRCYSqInst.shellOneTestOrderAeCGRCYSq_holds (𝒮 := 𝒮)
  have d6 := MatedCRT.Lemma68Window.shortWindow_hT_of_meanZero (hR := d1)
  have d7 := MatedCRT.LIClosed68Y.fieldVolCutoffStmt_of_berestyckiGwynne (𝒮 := 𝒮) (hBG := hBG)
  have d8 := MatedCRT.ShortWindowHV.wholePlaneUpperVolumeTailStep_of_ballMass (hBM := hBM) (hCC := hCC)
  have d9 := MatedCRT.CertifiedReferenceModel.cellSizeEstimate (h := hCRM)
  have d10 := MatedCRT.CertifiedReferenceModel.countingMeasureConvergence (h := hCRM)
  have d11 := MatedCRT.CertifiedReferenceModel.exitTimeUpperBound (h := hCRM)
  have d12 := MatedCRT.CertifiedReferenceModel.greenKernelLowerBound (h := hCRM)
  have d13 := MatedCRT.CountingExitAlpha68.countingAtExitAlphaStmt_of_counting_exit (hC := d10) (hE := d11)
  have d14 := MatedCRT.FirstPass64.firstPass_6_5_uniform (h0 := d3) (h2 := d2) (hV := d8)
  have d15 := MatedCRT.Lemma68Window.shortWindow_prevalence (h65 := d14) (hT := d6) (hL := d4)
  have d16 := MatedCRT.Lemma68CGRCY.countingMeshEventsHi_of_draft (𝒮 := 𝒮) (hG := d12) (hC := d9) (hK := d13)
  have d17 := MatedCRT.Lemma68CGRCYSq.shellChainCGRCYSq_of_oneTestOrderCGRCYSq (hprev := d15) (h := d5)
  have d18 := MatedCRT.Lemma68CGRCYSqHalf.guardProbStmtCGRCYSq_of_chain (𝒮 := 𝒮) (hMesh := d16) (hVol := d7)
    (hChain := d17)
  have d19 := MatedCRT.uniformConstantOrderLowerBound_of_guard (𝒮 := 𝒮) (hG := d18)
  MatedCRT.firstPass_6_9_faithful (𝒮 := 𝒮) (hU := d19)

end MatedCRT.LIClosed68Y
