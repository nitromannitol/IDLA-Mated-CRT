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
import MatedCRT.FirstPass.Derived.ConeDilationRatioHolds
import MatedCRT.FirstPass.Derived.ConeLogLocalCodeLawStdDerived
import MatedCRT.FirstPass.Derived.ConeReferenceExistsDerived
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
import MatedCRT.FirstPass.S6r.ShortWindow
import MatedCRT.FirstPass.S6r.ShortWindowClosed
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
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hscale : QuantumConeScalingInput)
    (hrescale : ConeRescaledMeasureIsConeFieldInput) :
    DivSandpileLowerBoundStmt 𝒮 :=
  have d1 := HarmonicBalls.firstPass_2_3
  have d2 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d3 := MatedCRT.FirstPass.Derived.coneReferenceExistsStep_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d6 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d7 := MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds
  have d8 := MatedCRT.HBRewire.FrozenGreenDiscPole_of_hb
  have d9 := MatedCRT.coneCircleAverageLocalityStep_proved
  have d10 := MatedCRT.coneCircleLawUniqueStep_holds
  have d11 := MatedCRT.fpStrongMinimumPrinciple_holds
  have d12 := MatedCRT.frozenGreenBallCentre_holds
  have d13 := MatedCRT.frozenLQGTestIntegralMeasurable_holds
  have d14 := MatedCRT.frozenPunctureConnected_holds
  have d15 := MatedCRT.frozenSuperharmonicMinimumPrinciple_holds
  have d16 := MatedCRT.frozenUniversalMeasurabilityOfAnalytic_holds
  have d17 := HarmonicBalls.clusterCompatibility_proved (hI2 := hI2)
  have d18 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := hI2)
  have d19 := HarmonicBalls.clusterMonotone_proved (hI2 := hI2)
  have d20 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := hI2)
  have d21 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := hI2)
  have d22 := MatedCRT.LQGMeasure.coneFieldScalingStep_proved_radial (hscale := hscale)
  have d23 := MatedCRT.LQGMeasure.lqgMeasureDilationCovariancePart_of_nonDyadic (hND := d7)
  have d24 := MatedCRT.MainHypotheses.maximumPrinciple (𝒮 := 𝒮)
  have d25 := MatedCRT.closed_4_4
  have d26 := MatedCRT.coneScaleRadiusPosStep_of_input (hscale := hscale)
  have d27 := MatedCRT.firstPass_2_17_ownBinders (hBG := hBG)
  have d28 := MatedCRT.obstacleLimitUniqueness (𝒮 := 𝒮)
  have d29 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := hI2)
  have d30 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d31 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := hExist) (h56 := d29)
  have d32 := MatedCRT.LQGMeasure.coneLQGScalingStep_of_dilation (hIV := d23) (hpos := d26)
  have d33 := MatedCRT.FirstPass35Bridge.discreteDirichletProblem_of_corrected_of_steps (h28 := h28) (h35c := h35c)
  have d34 := MatedCRT.LQGMeasure.lqgMeasureNonAtomicPart_of_scaling (h27 := d30) (hfield := d22) (hlqg := d32)
  have d35 := MatedCRT.LQGMeasure.lqgMeasureProperties_of_citedInputs (hNA := d34) (hCL := d9) (hND := d7)
  have d36 := MatedCRT.equibounded_of_boundedExitTime (h217 := d27) (h218 := h218) (hm := hm)
  have d37 := MatedCRT.discretePotentialTightnessAeStep_of_inputs (hm := hm) (h217 := d27) (h218 := h218) (hH := hH)
  have d38 := MatedCRT.strictGapDeterministicComparison_of_frozen (hG := d1) (hpc := d14) (hsmp := d11) (hwmp := d15)
    (hpole := d8)
  have d39 := MatedCRT.Audit.StatementsSec3Sec5M1.three_three_final_reduction (𝒮 := 𝒮) (h210 := h210) (h34 := h34)
    (h214 := h214) (h28 := h28) (hAe := d37)
  have d40 := MatedCRT.FirstPassClosure.coneHalfBallClosureInsideStep_proof (hI2 := hI2) (hK := d5) (hloc := hloc)
    (hEx := hExist) (hE := d6) (hFL := d2) (hBG := hBG)
  have d41 := MatedCRT.closed_2_5_lp_derivedInputs (hBdry := hBdry) (hExist := hExist) (hconf := hconf) (hI2 := hI2)
    (hloc := hloc) (hBG := hBG) (hscale := hscale)
  have d42 := MatedCRT.closed_2_3_lp_derivedInputs (hBG := hBG) (hscale := hscale) (hBdryHB := hBdry)
    (hExistHB := hExist) (hconf := hconf) (hI2HB := hI2) (hlocHB := hloc) (hrescale := hrescale)
  have d43 := MatedCRT.subsequentialPropertiesPrepared_of_identified_estimates (𝒮 := 𝒮) (hm := hm) (h47 := d36)
    (h44 := d25) (h33 := d39) (h35 := d33) (h218 := h218) (hH := hH) (h217 := d27) (h27 := d30)
  have d44 := MatedCRT.coneCanonicalHalfBallStep_of_draft (hU := d16) (hmeasT := d13) (hstd := d4) (hmin := d15)
    (hC := d12) (hGB := d1) (hpole := d8) (hOpen := d20) (hSup := d21) (hCons := d18) (hMono := d19) (hCompat := d17)
    (hBdry := hBdry) (hExist := hExist) (hThm11 := d31) (hProp56 := d29) (hconf := hconf)
  have d45 := MatedCRT.FirstPassClosure.strictGapFixedTimeUnionStep_proof_unconditional (hstd := d4) (hCentre := d12)
    (hOpen := d20) (hSup := d21) (hCons := d18) (hMono := d19) (hCompat := d17) (hBdry := hBdry) (hExist := hExist)
    (hThm11 := d31) (hProp56 := d29) (hconf := hconf) (hI2 := hI2) (hK := d5) (hloc := hloc) (hE := d6) (hFL := d2)
    (hBG := hBG) (hE1 := d10) (hE2 := d3) (hscale := hscale) (hND := d7) (hrescale := hrescale)
  have d46 := MatedCRT.coneHarmonicBallsUpToFixedTimeStmt_of_canonical (hcan := d44) (hcl := d40)
  have d47 := MatedCRT.coneRescaledHalfBallHorizonUnique_fp (hcan := d44) (hcl := d40) (hrescale := hrescale)
  have d48 := MatedCRT.harmonicBallStrictObstacleGapStep_of_steps (𝒮 := 𝒮) (hdet := d38) (hnj := d45)
  have d49 := MatedCRT.coneScaleInvarianceUpToFixedTimeStmt_of_canonical (hcan := d44) (hcl := d40) (hc25 := d41)
    (hU := d47)
  have d50 := MatedCRT.coneFamilyAEMeasurableStep_of_numbered_results (h24 := d46) (h25 := d49) (h27 := d30)
    (hscale := hscale) (h22 := d35)
  have d51 := MatedCRT.obstacleClusterInnerApproximation_of_strictGap (𝒮 := 𝒮) (h27 := d30) (hfam := d50) (h24 := d46)
    (hgap := d48)
  have d52 := MatedCRT.convergenceDivisibleEventMeasurableStep_of_coneFamilyAEMeasurable (𝒮 := 𝒮) (h27 := d30)
    (hfam := d50) (h24 := d46)
  have d53 := MatedCRT.convergenceDivisible_of_prepared_properties (𝒮 := 𝒮) (h48 := d43) (hu := d28) (hm := d52)
  MatedCRT.divSandpileLowerBound_of_inputs (𝒮 := 𝒮) (h41 := d53) (h23 := d42) (h213 := d24) (h33 := d39) (h28 := h28)
    (happrox := d51)

end MatedCRT.FirstPassClosure

namespace MatedCRT.LIClosed68Y

open MeasureTheory

/-- The conclusion of `MatedCRT.LIClosed68Y.firstPass_6_7_derivedInputs` (MatedCRT/FirstPass/Derived/Counted.lean) from its hypotheses without `hLit`, `hBM`, `hμ`: they are not needed. The remaining binders are copied unchanged. -/
theorem firstPass_6_7_minimalInputs
    {ν : ℝ → Measure SLEPathCode}
    {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    FaithfulConstantOrderLowerBoundStmt 𝒮 :=
  have d1 := MatedCRT.ConeMeanZeroRestriction.fpConeMeanZeroRestriction_holds
  have d2 := MatedCRT.FirstPass64.firstPass_6_5_uniform_derivedInputs
  have d3 := MatedCRT.Lemma68Window.shortWindow_hL_proved
  have d4 := MatedCRT.Lemma68CGRCYSqInst.shellOneTestOrderAeCGRCYSq_holds (𝒮 := 𝒮)
  have d5 := MatedCRT.Lemma68Window.shortWindow_hT_of_meanZero (hR := d1)
  have d6 := MatedCRT.LIClosed68Y.fieldVolCutoffStmt_of_berestyckiGwynne (𝒮 := 𝒮) (hBG := hBG)
  have d7 := MatedCRT.CertifiedReferenceModel.cellSizeEstimate (h := hCRM)
  have d8 := MatedCRT.CertifiedReferenceModel.countingMeasureConvergence (h := hCRM)
  have d9 := MatedCRT.CertifiedReferenceModel.exitTimeUpperBound (h := hCRM)
  have d10 := MatedCRT.CertifiedReferenceModel.greenKernelLowerBound (h := hCRM)
  have d11 := MatedCRT.CountingExitAlpha68.countingAtExitAlphaStmt_of_counting_exit (hC := d8) (hE := d9)
  have d12 := MatedCRT.Lemma68Window.shortWindow_prevalence (h65 := d2) (hT := d5) (hL := d3)
  have d13 := MatedCRT.Lemma68CGRCY.countingMeshEventsHi_of_draft (𝒮 := 𝒮) (hG := d10) (hC := d7) (hK := d11)
  have d14 := MatedCRT.Lemma68CGRCYSq.shellChainCGRCYSq_of_oneTestOrderCGRCYSq (hprev := d12) (h := d4)
  have d15 := MatedCRT.Lemma68CGRCYSqHalf.guardProbStmtCGRCYSq_of_chain (𝒮 := 𝒮) (hMesh := d13) (hVol := d6)
    (hChain := d14)
  have d16 := MatedCRT.uniformConstantOrderLowerBound_of_guard (𝒮 := 𝒮) (hG := d15)
  MatedCRT.firstPass_6_7_faithful (𝒮 := 𝒮) (hU := d16)

end MatedCRT.LIClosed68Y

namespace MatedCRT.LIClosed68Y

open MeasureTheory

/-- The conclusion of `MatedCRT.LIClosed68Y.firstPass_6_8_derivedInputs` (MatedCRT/FirstPass/Derived/Counted.lean) from its hypotheses without `hLit`, `hBM`, `hμ`: they are not needed. The remaining binders are copied unchanged. -/
theorem firstPass_6_8_minimalInputs
    {ν : ℝ → Measure SLEPathCode}
    {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    FaithfulConstantOrderLowerBoundDivStmt 𝒮 :=
  have d1 := MatedCRT.ConeMeanZeroRestriction.fpConeMeanZeroRestriction_holds
  have d2 := MatedCRT.FirstPass64.firstPass_6_5_uniform_derivedInputs
  have d3 := MatedCRT.Lemma68Window.shortWindow_hL_proved
  have d4 := MatedCRT.Lemma68CGRCYSqInst.shellOneTestOrderAeCGRCYSq_holds (𝒮 := 𝒮)
  have d5 := MatedCRT.Lemma68Window.shortWindow_hT_of_meanZero (hR := d1)
  have d6 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := hBG)
  have d7 := MatedCRT.LIClosed68Y.fieldVolCutoffStmt_of_berestyckiGwynne (𝒮 := 𝒮) (hBG := hBG)
  have d8 := MatedCRT.CertifiedReferenceModel.cellSizeEstimate (h := hCRM)
  have d9 := MatedCRT.CertifiedReferenceModel.countingMeasureConvergence (h := hCRM)
  have d10 := MatedCRT.CertifiedReferenceModel.exitTimeUpperBound (h := hCRM)
  have d11 := MatedCRT.CertifiedReferenceModel.greenKernelLowerBound (h := hCRM)
  have d12 := MatedCRT.CountingExitAlpha68.countingAtExitAlphaStmt_of_counting_exit (hC := d9) (hE := d10)
  have d13 := MatedCRT.Lemma68Window.shortWindow_prevalence (h65 := d2) (hT := d5) (hL := d3)
  have d14 := MatedCRT.Lemma68CGRCY.countingMeshEventsHi_of_draft (𝒮 := 𝒮) (hG := d11) (hC := d8) (hK := d12)
  have d15 := MatedCRT.Lemma68CGRCYSq.shellChainCGRCYSq_of_oneTestOrderCGRCYSq (hprev := d13) (h := d4)
  have d16 := MatedCRT.Lemma68CGRCYSqHalf.guardProbStmtCGRCYSq_of_chain (𝒮 := 𝒮) (hMesh := d14) (hVol := d7)
    (hChain := d15)
  have d17 := MatedCRT.uniformConstantOrderLowerBound_of_guard (𝒮 := 𝒮) (hG := d16)
  MatedCRT.firstPass_6_8_faithful (𝒮 := 𝒮) (hU := d17) (h27 := d6) (h28 := d8)

end MatedCRT.LIClosed68Y

namespace MatedCRT.LIClosed68Y

open MeasureTheory

/-- The conclusion of `MatedCRT.LIClosed68Y.firstPass_6_9_derivedInputs` (MatedCRT/FirstPass/Derived/Counted.lean) from its hypotheses without `hLit`, `hBM`, `hμ`: they are not needed. The remaining binders are copied unchanged. -/
theorem firstPass_6_9_minimalInputs
    {ν : ℝ → Measure SLEPathCode}
    {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    FaithfulChanceOfBeingAbsorbedStmt 𝒮 :=
  have d1 := MatedCRT.ConeMeanZeroRestriction.fpConeMeanZeroRestriction_holds
  have d2 := MatedCRT.FirstPass64.firstPass_6_5_uniform_derivedInputs
  have d3 := MatedCRT.Lemma68Window.shortWindow_hL_proved
  have d4 := MatedCRT.Lemma68CGRCYSqInst.shellOneTestOrderAeCGRCYSq_holds (𝒮 := 𝒮)
  have d5 := MatedCRT.Lemma68Window.shortWindow_hT_of_meanZero (hR := d1)
  have d6 := MatedCRT.LIClosed68Y.fieldVolCutoffStmt_of_berestyckiGwynne (𝒮 := 𝒮) (hBG := hBG)
  have d7 := MatedCRT.CertifiedReferenceModel.cellSizeEstimate (h := hCRM)
  have d8 := MatedCRT.CertifiedReferenceModel.countingMeasureConvergence (h := hCRM)
  have d9 := MatedCRT.CertifiedReferenceModel.exitTimeUpperBound (h := hCRM)
  have d10 := MatedCRT.CertifiedReferenceModel.greenKernelLowerBound (h := hCRM)
  have d11 := MatedCRT.CountingExitAlpha68.countingAtExitAlphaStmt_of_counting_exit (hC := d8) (hE := d9)
  have d12 := MatedCRT.Lemma68Window.shortWindow_prevalence (h65 := d2) (hT := d5) (hL := d3)
  have d13 := MatedCRT.Lemma68CGRCY.countingMeshEventsHi_of_draft (𝒮 := 𝒮) (hG := d10) (hC := d7) (hK := d11)
  have d14 := MatedCRT.Lemma68CGRCYSq.shellChainCGRCYSq_of_oneTestOrderCGRCYSq (hprev := d12) (h := d4)
  have d15 := MatedCRT.Lemma68CGRCYSqHalf.guardProbStmtCGRCYSq_of_chain (𝒮 := 𝒮) (hMesh := d13) (hVol := d6)
    (hChain := d14)
  have d16 := MatedCRT.uniformConstantOrderLowerBound_of_guard (𝒮 := 𝒮) (hG := d15)
  MatedCRT.firstPass_6_9_faithful (𝒮 := 𝒮) (hU := d16)

end MatedCRT.LIClosed68Y
