import MatedCRT.FirstPass.Phase2Rewire
import MatedCRT.FirstPass.S4d.FixedTimeFinal
import MatedCRT.FirstPass.S4d.Provider24
import MatedCRT.FirstPass.S4d.ScaleBridge
import MatedCRT.FirstPass.S4d.HorizonUnique
import MatedCRT.FirstPass.S2j
import MatedCRT.FirstPass.S2g.HalfBallGate
import MatedCRT.FirstPass.S5r.ClosureInside
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Proofs.Sec3.ConeBallMass
import MatedCRT.FirstPass.Frozen.S4d2

/-!
# Theorems 1.4 and 1.6 without the paper-step binders

`closed_1_4_p3` and `closed_1_6_p3` have the conclusions of `MatedCRT.Phase2.closed_1_4_derived_p2` and
`closed_1_6_derived_p2` (`FirstPass/Phase2Rewire.lean`), and the same binders except the six paper-step inputs
`hnj`, `hcan`, `hcl`, `h24c`, `hcan6`, `hcell`. Those are derived here:
* `hcan6` (canonical Lemma 2.4) from `Phase2.firstPass_2_4_canonical_p2`; `h24c` (corrected Lemma 2.4) from `hcan6`
  by `coneHarmonicBallsUpToFixedTimeCorrected_of_canonical`;
* `hcan` (`ConeCanonicalHalfBallStep`) from `coneCanonicalHalfBallStep_of_draft`; `hcl`
  (`ConeHalfBallClosureInsideStep`) from `S5r.coneHalfBallClosureInsideStep_corrected`;
* `hnj` (`StrictGapFixedTimeUnionStep`) from `strictGapFixedTimeUnionStep_of_provider` with the provider of `hcan6`,
  the Lemma 2.5 and 2.6 wrappers and `coneFamilyAEMeasurable_proved`;
* `hcell` from `adjacentCellsMeetAeStep`.
The one new binder is `hrescale : ConeRescaledMeasureIsConeFieldInput` (`FirstPass/Frozen/S4d2.lean:27`), the
cone-field input of `firstPass_4_2_of_wholeplane_model` (`FirstPass/S4d/Final42.lean:60`) and of the Lemma 2.5
horizon uniqueness.
-/

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls
open MatedCRT.FirstPassClosure

noncomputable section

namespace MatedCRT

/-- Corrected Lemma 2.4 (`ConeHarmonicBallsUpToFixedTimeCorrectedStmt`, `FirstPass/S2b.lean:43`) from its canonical form
(`ConeHarmonicBallsUpToFixedTimeCanonicalStmt`, `FirstPass/S2g.lean:38`). The time is `T = halfBallTime (μ ω)`, positive
almost surely; the uniqueness clause of `UniqueConeFamilyOn` is the `EqOn` clause of the corrected form. The measurability
clauses of the canonical form are dropped. -/
theorem coneHarmonicBallsUpToFixedTimeCorrected_of_canonical
    (hcan : ConeHarmonicBallsUpToFixedTimeCanonicalStmt) : ConeHarmonicBallsUpToFixedTimeCorrectedStmt := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone
  obtain ⟨_, Λ, _, hae⟩ := hcan γ hγ0 hγ2 Ω P hC hcirc μ hcone
  filter_upwards [hae] with ω hω
  obtain ⟨hpos, huniq, hstop⟩ := hω
  obtain ⟨hfam, hEq⟩ := huniq
  exact ⟨halfBallTime (μ ω), hpos, Λ ω, hfam, hstop, hEq⟩

/-- Theorem closed_1_4_p3 without the paper-step binders (audit B4): the `closed_1_4_derived_p2` conclusion with `hnj`, `hcan`, `hcl`, `h24c`, `hcan6`, `hcell` derived. -/
theorem closed_1_4_p3
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
    (hexc : FrozenBrownianOutwardExcursionAtExit)
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
    : ConvergenceOfIDLAStmt 𝒮 := by
  have h27 : VolumeGrowthStmt := volumeGrowthStmt_of_berestyckiGwynne hBG
  have hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt :=
    MatedCRT.Phase2.firstPass_2_4_canonical_p2 (hstd := hstd) (hCentre := hGBC) (hOpen := h32) (hSup := hSup)
      (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hExist := hEx) (hThm11 := hThm11)
      (hProp56 := hProp56) (hconf := hconf) (hI2 := hI2) (hK := hK) (hloc := hloc) (hSC := hSC) (hE := hE)
      (hFL := hFL) (h27 := h27)
  have hcan : ConeCanonicalHalfBallStep :=
    coneCanonicalHalfBallStep_of_draft MatedCRT.frozenUniversalMeasurabilityOfAnalytic_holds
      MatedCRT.frozenLQGTestIntegralMeasurable_holds hstd MatedCRT.frozenSuperharmonicMinimumPrinciple_holds hGBC
      MatedCRT.HBRewire.GreenFunctionBallStmt_of_hb MatedCRT.HBRewire.FrozenGreenDiscPole_of_hb h32 hSup hCons hMono
      hCompat hBdry hEx hThm11 hProp56 hconf
  have hcl : ConeHalfBallClosureInsideStep :=
    MatedCRT.S5r.coneHalfBallClosureInsideStep_corrected hI2 hK hloc hEx hSC h27 hE hFL
  have hprov : ConeHarmonicBallsProviderFP4 := coneHarmonicBallsProviderFP4_of_canonical hcan6
  have hc25 : ConeScaleInvarianceUpToFixedTimeCanonicalStmt :=
    MatedCRT.Phase2.firstPass_2_5_canonical_p2 (hstd := hstd) (hCentre := hGBC) (hOpen := h32) (hSup := hSup)
      (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hExist := hEx) (hThm11 := hThm11)
      (hProp56 := hProp56) (hconf := hconf) (hI2 := hI2) (hK := hK) (hloc := hloc) (hSC := hSC) (hE := hE)
      (hFL := hFL) (h27 := h27) (hE1 := hE1) (hE2 := hE2) (hscale := hscale) (h22 := h22)
  have h25 : ConeScaleInvarianceUpToFixedTimeStmt :=
    coneScaleInvarianceUpToFixedTimeStmt_of_canonical hcan hcl hc25 (coneRescaledHalfBallHorizonUnique_fp hcan hcl hrescale)
  have hfam : ConeFamilyAEMeasurableStep := coneFamilyAEMeasurable_proved hcan hcl h27 hE1 hE2 hscale h22
  have h26 : ConeScaleInvarianceStmt :=
    MatedCRT.Phase2.firstPass_2_6_corrected_p2 (hstd := hstd) (hCentre := hGBC) (hOpen := h32) (hSup := hSup)
      (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hExist := hEx) (hThm11 := hThm11)
      (hProp56 := hProp56) (hconf := hconf) (hI2 := hI2) (hK := hK) (hloc := hloc) (hSC := hSC) (hE := hE)
      (hFL := hFL) (h27 := h27) (hE1 := hE1) (hE2 := hE2) (hscale := hscale) (h22 := h22)
  have hnj : StrictGapFixedTimeUnionStep 𝒮 := strictGapFixedTimeUnionStep_of_provider 𝒮 hprov h25 hfam h26 hscale
  have hcell : FrozenAdjacentCellsMeetAe 𝒮 := adjacentCellsMeetAeStep 𝒮
  have h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt := coneHarmonicBallsUpToFixedTimeCorrected_of_canonical hcan6
  exact MatedCRT.Phase2.closed_1_4_derived_p2 (𝒮 := 𝒮) (ν := ν) (hC := hC) (hscale := hscale) (hsc := hsc) (hrp := hrp) (hind := hind) (hEnvS := hEnvS) (hm := hm) (hdeg := hdeg) (hBG := hBG) (h28 := h28) (h29 := h29) (h210 := h210) (h214 := h214) (h216 := h216) (h51 := h51) (hH := hH) (h0 := h0) (h2 := h2) (hV := hV) (hR := hR) (hcone := hcone) (hrevuz := hrevuz) (h23 := h23) (hdiv := hdiv) (hF3 := hF3) (hexc := hexc) (hsup := hsup) (hmodel := hmodel) (hFL := hFL) (hstd := hstd) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (h22 := h22) (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc) (hSC := hSC) (hnj := hnj) (hcan := hcan) (hcl := hcl) (hcan6 := hcan6) (h24c := h24c) (hcell := hcell)

/-- Theorem closed_1_6_p3 without the paper-step binders (audit B4): the `closed_1_6_derived_p2` conclusion with `hnj`, `hcan`, `hcl`, `h24c`, `hcan6`, `hcell` derived. -/
theorem closed_1_6_p3
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
    (hexc : FrozenBrownianOutwardExcursionAtExit)
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
    : ConvergenceOfDivSandpileStmt 𝒮 := by
  have h27 : VolumeGrowthStmt := volumeGrowthStmt_of_berestyckiGwynne hBG
  have hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt :=
    MatedCRT.Phase2.firstPass_2_4_canonical_p2 (hstd := hstd) (hCentre := hGBC) (hOpen := h32) (hSup := hSup)
      (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hExist := hEx) (hThm11 := hThm11)
      (hProp56 := hProp56) (hconf := hconf) (hI2 := hI2) (hK := hK) (hloc := hloc) (hSC := hSC) (hE := hE)
      (hFL := hFL) (h27 := h27)
  have hcan : ConeCanonicalHalfBallStep :=
    coneCanonicalHalfBallStep_of_draft MatedCRT.frozenUniversalMeasurabilityOfAnalytic_holds
      MatedCRT.frozenLQGTestIntegralMeasurable_holds hstd MatedCRT.frozenSuperharmonicMinimumPrinciple_holds hGBC
      MatedCRT.HBRewire.GreenFunctionBallStmt_of_hb MatedCRT.HBRewire.FrozenGreenDiscPole_of_hb h32 hSup hCons hMono
      hCompat hBdry hEx hThm11 hProp56 hconf
  have hcl : ConeHalfBallClosureInsideStep :=
    MatedCRT.S5r.coneHalfBallClosureInsideStep_corrected hI2 hK hloc hEx hSC h27 hE hFL
  have hprov : ConeHarmonicBallsProviderFP4 := coneHarmonicBallsProviderFP4_of_canonical hcan6
  have hc25 : ConeScaleInvarianceUpToFixedTimeCanonicalStmt :=
    MatedCRT.Phase2.firstPass_2_5_canonical_p2 (hstd := hstd) (hCentre := hGBC) (hOpen := h32) (hSup := hSup)
      (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hExist := hEx) (hThm11 := hThm11)
      (hProp56 := hProp56) (hconf := hconf) (hI2 := hI2) (hK := hK) (hloc := hloc) (hSC := hSC) (hE := hE)
      (hFL := hFL) (h27 := h27) (hE1 := hE1) (hE2 := hE2) (hscale := hscale) (h22 := h22)
  have h25 : ConeScaleInvarianceUpToFixedTimeStmt :=
    coneScaleInvarianceUpToFixedTimeStmt_of_canonical hcan hcl hc25 (coneRescaledHalfBallHorizonUnique_fp hcan hcl hrescale)
  have hfam : ConeFamilyAEMeasurableStep := coneFamilyAEMeasurable_proved hcan hcl h27 hE1 hE2 hscale h22
  have h26 : ConeScaleInvarianceStmt :=
    MatedCRT.Phase2.firstPass_2_6_corrected_p2 (hstd := hstd) (hCentre := hGBC) (hOpen := h32) (hSup := hSup)
      (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hExist := hEx) (hThm11 := hThm11)
      (hProp56 := hProp56) (hconf := hconf) (hI2 := hI2) (hK := hK) (hloc := hloc) (hSC := hSC) (hE := hE)
      (hFL := hFL) (h27 := h27) (hE1 := hE1) (hE2 := hE2) (hscale := hscale) (h22 := h22)
  have hnj : StrictGapFixedTimeUnionStep 𝒮 := strictGapFixedTimeUnionStep_of_provider 𝒮 hprov h25 hfam h26 hscale
  have hcell : FrozenAdjacentCellsMeetAe 𝒮 := adjacentCellsMeetAeStep 𝒮
  have h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt := coneHarmonicBallsUpToFixedTimeCorrected_of_canonical hcan6
  exact MatedCRT.Phase2.closed_1_6_derived_p2 (𝒮 := 𝒮) (ν := ν) (hC := hC) (hscale := hscale) (hsc := hsc) (hrp := hrp) (hind := hind) (hEnvS := hEnvS) (hm := hm) (hdeg := hdeg) (hBG := hBG) (h28 := h28) (h29 := h29) (h210 := h210) (h214 := h214) (h216 := h216) (h51 := h51) (hH := hH) (h0 := h0) (h2 := h2) (hV := hV) (hR := hR) (hcone := hcone) (hrevuz := hrevuz) (h23 := h23) (hdiv := hdiv) (hF3 := hF3) (hexc := hexc) (hsup := hsup) (hmodel := hmodel) (hFL := hFL) (hstd := hstd) (hGBC := hGBC) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (h22 := h22) (hG15 := hG15) (h32 := h32) (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc) (hSC := hSC) (hnj := hnj) (hcan := hcan) (hcl := hcl) (hcan6 := hcan6) (h24c := h24c) (hcell := hcell)

end MatedCRT

#print axioms MatedCRT.closed_1_4_p3
#print axioms MatedCRT.closed_1_6_p3
