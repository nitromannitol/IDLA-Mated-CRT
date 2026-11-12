import HarmonicBalls.Assembly.ExistenceUniqueness
import HarmonicBalls.FirstPass.Closure
import HarmonicBalls.Proofs.Sec3.Basic
import HarmonicBalls.Proofs.Sec3.ClusterCompatibility
import HarmonicBalls.Proofs.Sec3.ConservationOfMassLemma
import HarmonicBalls.Proofs.Sec3.OpenLaplacian
import HarmonicBalls.Proofs.Sec6.VolumeGrowthConsequences
import MatedCRT.Assembly.Main
import MatedCRT.Audit.StatementsSec3Sec5M1
import MatedCRT.FirstPass.Closure.Section4
import MatedCRT.FirstPass.Closure.Steps42
import MatedCRT.FirstPass.Derived.ConeDilationRatioHolds
import MatedCRT.FirstPass.Derived.ConeLogLocalCodeLawStdDerived
import MatedCRT.FirstPass.Derived.ConeRescaledFieldHolds
import MatedCRT.FirstPass.Derived.ConeWholePlaneFieldLaw
import MatedCRT.FirstPass.Derived.Counted
import MatedCRT.FirstPass.Derived.DiscGreenCentre
import MatedCRT.FirstPass.Derived.HBBallMassHolds
import MatedCRT.FirstPass.Derived.HarmonicBallsVolumeGrowth
import MatedCRT.FirstPass.Derived.InsertionCoordinateRule
import MatedCRT.FirstPass.Derived.LQGMeasureInputs
import MatedCRT.FirstPass.HBRewire
import MatedCRT.FirstPass.LIClosed68Y
import MatedCRT.FirstPass.LPBridge.ConeMeanZeroRestrictionFinal
import MatedCRT.FirstPass.LPBridge.LQGTestIntegralMeasurable
import MatedCRT.FirstPass.LPBridge.MinimumPrinciples
import MatedCRT.FirstPass.LPBridge.PairingLawIG4
import MatedCRT.FirstPass.LPBridge.UniversalMeasurability
import MatedCRT.FirstPass.S2g.Draft24
import MatedCRT.FirstPass.S2g.HalfBallGate
import MatedCRT.FirstPass.S2m
import MatedCRT.FirstPass.S2y.ConeCircleAbsApprox
import MatedCRT.FirstPass.S2y.LateralAssembly250
import MatedCRT.FirstPass.S3g
import MatedCRT.FirstPass.S4S5b
import MatedCRT.FirstPass.S4S6c.CGRCYSqInst68
import MatedCRT.FirstPass.S4S6c.CountingExitAlpha68
import MatedCRT.FirstPass.S4S6c.ShellChainCGRCY68
import MatedCRT.FirstPass.S4S6c.ShellChainCGRCYSq68
import MatedCRT.FirstPass.S4S6c.ShellChainCGRCYSqHalf68
import MatedCRT.FirstPass.S4S6c.Uniform68Final
import MatedCRT.FirstPass.S4d.HorizonUnique
import MatedCRT.FirstPass.S4d.ScaleBridge
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
import MatedCRT.Proofs.Sec4.Prop42Closure.LQGMeasureLocalityProof
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
    (hscale : QuantumConeScalingInput) :
    DivSandpileLowerBoundStmt 𝒮 :=
  have d1 := HarmonicBalls.Closure.closure_2_3
  have d2 := MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds
  have d3 := MatedCRT.FirstPass.Derived.existenceHarmonicBallsStmt_holds
  have d4 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  have d5 := MatedCRT.FirstPass.Derived.frozenClusterBoundaryMeasureZero_holds
  have d6 := MatedCRT.FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
  have d7 := MatedCRT.FirstPass.Derived.frozenHBInitialConfinement_holds
  have d8 := MatedCRT.FirstPass.Derived.frozenInsertionCoordinateRule_holds
  have d9 := MatedCRT.FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
  have d10 := MatedCRT.FirstPass.Derived.frozenLQGVolumeGrowthAllScales_holds
  have d11 := MatedCRT.FirstPass.Derived.frozenTypicalPointManyGoodScales_holds
  have d12 := MatedCRT.FirstPass.Derived.harmonicBallLocalSetStmt_holds
  have d13 := MatedCRT.FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds
  have d14 := MatedCRT.HBRewire.FrozenGreenDiscPole_of_hb
  have d15 := MatedCRT.LQGMeasureLocalityFunctionalStep_proof
  have d16 := MatedCRT.coneCircleAverageLocalityStep_proved
  have d17 := MatedCRT.firstPass_2_17_ownBinders_derivedInputs
  have d18 := MatedCRT.fpPairingLawIG4_holds
  have d19 := MatedCRT.frozenGreenBallCentre_holds
  have d20 := MatedCRT.frozenLQGTestIntegralMeasurable_holds
  have d21 := MatedCRT.frozenSuperharmonicMinimumPrinciple_holds
  have d22 := MatedCRT.frozenUniversalMeasurabilityOfAnalytic_holds
  have d23 := HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only (hI2 := d10)
  have d24 := HarmonicBalls.clusterCompatibility_proved (hI2 := d10)
  have d25 := HarmonicBalls.clusterConservationOfMass_proved (hI2 := d10)
  have d26 := HarmonicBalls.clusterMonotone_proved (hI2 := d10)
  have d27 := HarmonicBalls.clusterOpenLaplacian_proved (hI2 := d10)
  have d28 := HarmonicBalls.leastSupersolutionMem_proved (hI2 := d10)
  have d29 := MatedCRT.FirstPass.Derived.coneRescaledMeasureIsConeFieldInput_of_scaling (hscale := hscale)
  have d30 := MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence (hE := d9)
  have d31 := MatedCRT.LQGMeasure.coneFieldScalingStep_proved_radial (hscale := hscale)
  have d32 := MatedCRT.LQGMeasure.lqgMeasureDilationCovariancePart_of_nonDyadic (hND := d13)
  have d33 := MatedCRT.MainHypotheses.maximumPrinciple (𝒮 := 𝒮)
  have d34 := MatedCRT.closed_2_3_lp_derivedInputs (hscale := hscale)
  have d35 := MatedCRT.closed_2_5_lp_derivedInputs (hscale := hscale)
  have d36 := MatedCRT.closed_4_4
  have d37 := MatedCRT.coneScaleRadiusPosStep_of_input (hscale := hscale)
  have d38 := MatedCRT.obstacleLimitUniqueness (𝒮 := 𝒮)
  have d39 := MatedCRT.uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := d10)
  have d40 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := d4)
  have d41 := HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := d3) (h56 := d39)
  have d42 := MatedCRT.LQGMeasure.coneLQGScalingStep_of_dilation (hIV := d32) (hpos := d37)
  have d43 := MatedCRT.FirstPass35Bridge.discreteDirichletProblem_of_corrected_of_steps (h28 := h28) (h35c := h35c)
  have d44 := MatedCRT.LQGMeasure.lqgMeasureNonAtomicPart_of_scaling (h27 := d40) (hfield := d31) (hlqg := d42)
  have d45 := MatedCRT.LQGMeasure.lqgMeasureProperties_of_citedInputs (hNA := d44) (hCL := d16) (hND := d13)
  have d46 := MatedCRT.equibounded_of_boundedExitTime (h217 := d17) (h218 := h218) (hm := hm)
  have d47 := MatedCRT.discretePotentialTightnessAeStep_of_inputs (hm := hm) (h217 := d17) (h218 := h218) (hH := hH)
  have d48 := MatedCRT.Audit.StatementsSec3Sec5M1.three_three_final_reduction (𝒮 := 𝒮) (h210 := h210) (h34 := h34)
    (h214 := h214) (h28 := h28) (hAe := d47)
  have d49 := MatedCRT.FirstPassClosure.coneHalfBallClosureInsideStep_proof (hI2 := d10) (hK := d8) (hloc := d12)
    (hEx := d3) (hE := d9) (hFL := d2) (hBG := d4)
  have d50 := MatedCRT.firstPass_strictObstacleGap (𝒮 := 𝒮) (h32 := d27) (h611 := d23) (h82 := d11) (hI2 := d10)
    (h27 := d40) (hmodel := d30) (hFL := d2) (hLoc := d15) (hpair := d18)
  have d51 := MatedCRT.subsequentialPropertiesPrepared_of_identified_estimates (𝒮 := 𝒮) (hm := hm) (h47 := d46)
    (h44 := d36) (h33 := d48) (h35 := d43) (h218 := h218) (hH := hH) (h217 := d17) (h27 := d40)
  have d52 := MatedCRT.coneCanonicalHalfBallStep_of_draft (hU := d22) (hmeasT := d20) (hstd := d6) (hmin := d21)
    (hC := d19) (hGB := d1) (hpole := d14) (hOpen := d27) (hSup := d28) (hCons := d25) (hMono := d26) (hCompat := d24)
    (hBdry := d5) (hExist := d3) (hThm11 := d41) (hProp56 := d39) (hconf := d7)
  have d53 := MatedCRT.coneHarmonicBallsUpToFixedTimeStmt_of_canonical (hcan := d52) (hcl := d49)
  have d54 := MatedCRT.coneRescaledHalfBallHorizonUnique_fp (hcan := d52) (hcl := d49) (hrescale := d29)
  have d55 := MatedCRT.coneScaleInvarianceUpToFixedTimeStmt_of_canonical (hcan := d52) (hcl := d49) (hc25 := d35)
    (hU := d54)
  have d56 := MatedCRT.coneFamilyAEMeasurableStep_of_numbered_results (h24 := d53) (h25 := d55) (h27 := d40)
    (hscale := hscale) (h22 := d45)
  have d57 := MatedCRT.obstacleClusterInnerApproximation_of_strictGap (𝒮 := 𝒮) (h27 := d40) (hfam := d56) (h24 := d53)
    (hgap := d50)
  have d58 := MatedCRT.convergenceDivisibleEventMeasurableStep_of_coneFamilyAEMeasurable (𝒮 := 𝒮) (h27 := d40)
    (hfam := d56) (h24 := d53)
  have d59 := MatedCRT.convergenceDivisible_of_prepared_properties (𝒮 := 𝒮) (h48 := d51) (hu := d38) (hm := d58)
  MatedCRT.divSandpileLowerBound_of_inputs (𝒮 := 𝒮) (h41 := d59) (h23 := d34) (h213 := d33) (h33 := d48) (h28 := h28)
    (happrox := d57)

end MatedCRT.FirstPassClosure

namespace MatedCRT.LIClosed68Y

open MeasureTheory

/-- The conclusion of `MatedCRT.LIClosed68Y.firstPass_6_7_derivedInputs` (MatedCRT/FirstPass/Derived/Counted.lean) from its hypotheses without `hLit`, `hBM`, `hμ`: they are not needed. The remaining binders are copied unchanged. -/
theorem firstPass_6_7_minimalInputs
    {ν : ℝ → Measure SLEPathCode}
    {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮) :
    FaithfulConstantOrderLowerBoundStmt 𝒮 :=
  have d1 := MatedCRT.ConeMeanZeroRestriction.fpConeMeanZeroRestriction_holds
  have d2 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  have d3 := MatedCRT.FirstPass64.firstPass_6_5_uniform_derivedInputs
  have d4 := MatedCRT.Lemma68Window.shortWindow_hL_proved
  have d5 := MatedCRT.Lemma68CGRCYSqInst.shellOneTestOrderAeCGRCYSq_holds (𝒮 := 𝒮)
  have d6 := MatedCRT.Lemma68Window.shortWindow_hT_of_meanZero (hR := d1)
  have d7 := MatedCRT.LIClosed68Y.fieldVolCutoffStmt_of_berestyckiGwynne (𝒮 := 𝒮) (hBG := d2)
  have d8 := MatedCRT.CertifiedReferenceModel.cellSizeEstimate (h := hCRM)
  have d9 := MatedCRT.CertifiedReferenceModel.countingMeasureConvergence (h := hCRM)
  have d10 := MatedCRT.CertifiedReferenceModel.exitTimeUpperBound (h := hCRM)
  have d11 := MatedCRT.CertifiedReferenceModel.greenKernelLowerBound (h := hCRM)
  have d12 := MatedCRT.CountingExitAlpha68.countingAtExitAlphaStmt_of_counting_exit (hC := d9) (hE := d10)
  have d13 := MatedCRT.Lemma68Window.shortWindow_prevalence (h65 := d3) (hT := d6) (hL := d4)
  have d14 := MatedCRT.Lemma68CGRCY.countingMeshEventsHi_of_draft (𝒮 := 𝒮) (hG := d11) (hC := d8) (hK := d12)
  have d15 := MatedCRT.Lemma68CGRCYSq.shellChainCGRCYSq_of_oneTestOrderCGRCYSq (hprev := d13) (h := d5)
  have d16 := MatedCRT.Lemma68CGRCYSqHalf.guardProbStmtCGRCYSq_of_chain (𝒮 := 𝒮) (hMesh := d14) (hVol := d7)
    (hChain := d15)
  have d17 := MatedCRT.uniformConstantOrderLowerBound_of_guard (𝒮 := 𝒮) (hG := d16)
  MatedCRT.firstPass_6_7_faithful (𝒮 := 𝒮) (hU := d17)

end MatedCRT.LIClosed68Y

namespace MatedCRT.LIClosed68Y

open MeasureTheory

/-- The conclusion of `MatedCRT.LIClosed68Y.firstPass_6_8_derivedInputs` (MatedCRT/FirstPass/Derived/Counted.lean) from its hypotheses without `hLit`, `hBM`, `hμ`: they are not needed. The remaining binders are copied unchanged. -/
theorem firstPass_6_8_minimalInputs
    {ν : ℝ → Measure SLEPathCode}
    {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮) :
    FaithfulConstantOrderLowerBoundDivStmt 𝒮 :=
  have d1 := MatedCRT.ConeMeanZeroRestriction.fpConeMeanZeroRestriction_holds
  have d2 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  have d3 := MatedCRT.FirstPass64.firstPass_6_5_uniform_derivedInputs
  have d4 := MatedCRT.Lemma68Window.shortWindow_hL_proved
  have d5 := MatedCRT.Lemma68CGRCYSqInst.shellOneTestOrderAeCGRCYSq_holds (𝒮 := 𝒮)
  have d6 := MatedCRT.Lemma68Window.shortWindow_hT_of_meanZero (hR := d1)
  have d7 := MatedCRT.volumeGrowthStmt_of_berestyckiGwynne (hBG := d2)
  have d8 := MatedCRT.LIClosed68Y.fieldVolCutoffStmt_of_berestyckiGwynne (𝒮 := 𝒮) (hBG := d2)
  have d9 := MatedCRT.CertifiedReferenceModel.cellSizeEstimate (h := hCRM)
  have d10 := MatedCRT.CertifiedReferenceModel.countingMeasureConvergence (h := hCRM)
  have d11 := MatedCRT.CertifiedReferenceModel.exitTimeUpperBound (h := hCRM)
  have d12 := MatedCRT.CertifiedReferenceModel.greenKernelLowerBound (h := hCRM)
  have d13 := MatedCRT.CountingExitAlpha68.countingAtExitAlphaStmt_of_counting_exit (hC := d10) (hE := d11)
  have d14 := MatedCRT.Lemma68Window.shortWindow_prevalence (h65 := d3) (hT := d6) (hL := d4)
  have d15 := MatedCRT.Lemma68CGRCY.countingMeshEventsHi_of_draft (𝒮 := 𝒮) (hG := d12) (hC := d9) (hK := d13)
  have d16 := MatedCRT.Lemma68CGRCYSq.shellChainCGRCYSq_of_oneTestOrderCGRCYSq (hprev := d14) (h := d5)
  have d17 := MatedCRT.Lemma68CGRCYSqHalf.guardProbStmtCGRCYSq_of_chain (𝒮 := 𝒮) (hMesh := d15) (hVol := d8)
    (hChain := d16)
  have d18 := MatedCRT.uniformConstantOrderLowerBound_of_guard (𝒮 := 𝒮) (hG := d17)
  MatedCRT.firstPass_6_8_faithful (𝒮 := 𝒮) (hU := d18) (h27 := d7) (h28 := d9)

end MatedCRT.LIClosed68Y

namespace MatedCRT.LIClosed68Y

open MeasureTheory

/-- The conclusion of `MatedCRT.LIClosed68Y.firstPass_6_9_derivedInputs` (MatedCRT/FirstPass/Derived/Counted.lean) from its hypotheses without `hLit`, `hBM`, `hμ`: they are not needed. The remaining binders are copied unchanged. -/
theorem firstPass_6_9_minimalInputs
    {ν : ℝ → Measure SLEPathCode}
    {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮) :
    FaithfulChanceOfBeingAbsorbedStmt 𝒮 :=
  have d1 := MatedCRT.ConeMeanZeroRestriction.fpConeMeanZeroRestriction_holds
  have d2 := MatedCRT.FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  have d3 := MatedCRT.FirstPass64.firstPass_6_5_uniform_derivedInputs
  have d4 := MatedCRT.Lemma68Window.shortWindow_hL_proved
  have d5 := MatedCRT.Lemma68CGRCYSqInst.shellOneTestOrderAeCGRCYSq_holds (𝒮 := 𝒮)
  have d6 := MatedCRT.Lemma68Window.shortWindow_hT_of_meanZero (hR := d1)
  have d7 := MatedCRT.LIClosed68Y.fieldVolCutoffStmt_of_berestyckiGwynne (𝒮 := 𝒮) (hBG := d2)
  have d8 := MatedCRT.CertifiedReferenceModel.cellSizeEstimate (h := hCRM)
  have d9 := MatedCRT.CertifiedReferenceModel.countingMeasureConvergence (h := hCRM)
  have d10 := MatedCRT.CertifiedReferenceModel.exitTimeUpperBound (h := hCRM)
  have d11 := MatedCRT.CertifiedReferenceModel.greenKernelLowerBound (h := hCRM)
  have d12 := MatedCRT.CountingExitAlpha68.countingAtExitAlphaStmt_of_counting_exit (hC := d9) (hE := d10)
  have d13 := MatedCRT.Lemma68Window.shortWindow_prevalence (h65 := d3) (hT := d6) (hL := d4)
  have d14 := MatedCRT.Lemma68CGRCY.countingMeshEventsHi_of_draft (𝒮 := 𝒮) (hG := d11) (hC := d8) (hK := d12)
  have d15 := MatedCRT.Lemma68CGRCYSq.shellChainCGRCYSq_of_oneTestOrderCGRCYSq (hprev := d13) (h := d5)
  have d16 := MatedCRT.Lemma68CGRCYSqHalf.guardProbStmtCGRCYSq_of_chain (𝒮 := 𝒮) (hMesh := d14) (hVol := d7)
    (hChain := d15)
  have d17 := MatedCRT.uniformConstantOrderLowerBound_of_guard (𝒮 := 𝒮) (hG := d16)
  MatedCRT.firstPass_6_9_faithful (𝒮 := 𝒮) (hU := d17)

end MatedCRT.LIClosed68Y
