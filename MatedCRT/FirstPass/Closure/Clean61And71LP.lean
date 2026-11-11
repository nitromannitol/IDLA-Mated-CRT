import MatedCRT.FirstPass.Closure.Clean61And81
import MatedCRT.FirstPass.Closure.Clean71
import MatedCRT.FirstPass.HBRewire
import MatedCRT.FirstPass.LPBridge.InRepoProofs
import MatedCRT.FirstPass.LPBridge.FiniteMeasureStandardBorel
import MatedCRT.FirstPass.LPBridge.UniversalMeasurability
import MatedCRT.FirstPass.LPBridge.BrownianOutwardExcursion
import MatedCRT.FirstPass.LPBridge.LQGTestIntegralMeasurable
import MatedCRT.FirstPass.LPBridge.MinimumPrinciples
import MatedCRT.FirstPass.LPBridge.PairingLawIG4
import MatedCRT.FirstPass.LPBridge.ConeMeanZeroRestrictionFinal

/-!
# Propositions 6.1 and 7.1 with the LP-bridge binders discharged

`closed_6_1_lp` and `closed_7_1_lp` have the conclusions of `closed_6_1_clean`
(`Closure/Clean61And81.lean:31`) and `closed_7_1_clean` (`Closure/Clean71.lean:42`). Each binder below is discharged
only when a committed concluder has exactly the binder's type and no hypotheses of its own:

Proposition 6.1 (11 of its 42 hypotheses):
* `hμae : FrozenLQGMeasureFieldMeasurable 𝒮` ← `frozenLQGMeasureFieldMeasurable_holds 𝒮` (LPBridge/InRepoProofs.lean:35);
* `hSB : FrozenFiniteMeasureDiskStandardBorel` ← `frozenFiniteMeasureDiskStandardBorel_holds` (LPBridge/FiniteMeasureStandardBorel.lean:18);
* `hU : FrozenUniversalMeasurabilityOfAnalytic` ← `frozenUniversalMeasurabilityOfAnalytic_holds` (LPBridge/UniversalMeasurability.lean:18);
* `hexc : FrozenBrownianOutwardExcursionAtExit` ← `frozenBrownianOutwardExcursionAtExit_holds` (LPBridge/BrownianOutwardExcursion.lean:113);
* `hpole : FrozenGreenDiscPole` ← `HBRewire.FrozenGreenDiscPole_of_hb` (FirstPass/HBRewire.lean:40);
* `hLoc : FPLQGMeasureLocality` ← `fpLQGMeasureLocality_holds` (LPBridge/InRepoProofs.lean:45);
* `hpair : FPPairingLawIG4` ← `fpPairingLawIG4_holds` (LPBridge/PairingLawIG4.lean:81);
* `hmeasT : FrozenLQGTestIntegralMeasurable` ← `frozenLQGTestIntegralMeasurable_holds` (LPBridge/LQGTestIntegralMeasurable.lean:49);
* `hmin : FrozenSuperharmonicMinimumPrinciple` ← `frozenSuperharmonicMinimumPrinciple_holds` (LPBridge/MinimumPrinciples.lean:22);
* `hR : FPConeMeanZeroRestriction` ← `ConeMeanZeroRestriction.fpConeMeanZeroRestriction_holds` (LPBridge/ConeMeanZeroRestrictionFinal.lean:144);
* `hGB : GreenFunctionBallStmt` ← `HBRewire.GreenFunctionBallStmt_of_hb` (FirstPass/HBRewire.lean:33).

Proposition 7.1 (7 of its 34 hypotheses): `hexc`, `hU`, `hmeasT`, `hmin`, `hGB`, `hpole`, `hR`, with the same concluders.
-/

open MeasureTheory Set
open _root_.HarmonicBalls

namespace MatedCRT

/-- **Proposition 6.1, LP-bridge form.** The conclusion is `IDLAUpperBoundStmt 𝒮`, as for `closed_6_1_clean`, with the
eleven binders listed in the module docstring discharged. -/
theorem closed_6_1_lp {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮)
    (hmodel : FPWholePlaneLQGModel) (hFL : FPConeWholePlaneFieldLaw)
    (hstd : FrozenConeLogLocalCodeLawStd) (hCentre : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (hND : LQGMeasureNonDyadicDilationPart)
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
    (hOpen : ClusterOpenLaplacianStmt.{0}) (h611 : VeryGoodAnnulusHarnackTypeStmt.{0})
    (h82 : TypicalPointManyGoodScalesStmt.{0}) (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0}) (hExist : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hloc : HarmonicBallLocalSetStmt.{0}) (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail) :
    IDLAUpperBoundStmt 𝒮 :=
  closed_6_1_clean (𝒮 := 𝒮) (ν := ν) (hC := hC)
    (hμae := frozenLQGMeasureFieldMeasurable_holds 𝒮)
    (hSB := frozenFiniteMeasureDiskStandardBorel_holds)
    (hsup := hsup) (hU := frozenUniversalMeasurabilityOfAnalytic_holds)
    (hexc := frozenBrownianOutwardExcursionAtExit_holds)
    (hpole := HBRewire.FrozenGreenDiscPole_of_hb)
    (hmodel := hmodel) (hFL := hFL)
    (hLoc := fpLQGMeasureLocality_holds) (hpair := fpPairingLawIG4_holds)
    (hmeasT := frozenLQGTestIntegralMeasurable_holds)
    (hstd := hstd) (hmin := frozenSuperharmonicMinimumPrinciple_holds)
    (hCentre := hCentre) (hconf := hconf) (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2)
    (hscale := hscale) (hND := hND) (hcanon := hcanon)
    (hOpen := hOpen) (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons)
    (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hExist := hExist) (hThm11 := hThm11)
    (hProp56 := hProp56) (hloc := hloc) (hBG := hBG) (h0 := h0) (h2 := h2) (hV := hV)
    (hR := ConeMeanZeroRestriction.fpConeMeanZeroRestriction_holds)
    (hGB := HBRewire.GreenFunctionBallStmt_of_hb)

/-- **Proposition 7.1, LP-bridge form.** The conclusion is `DivSandpileUpperBoundStmt 𝒮`, as for `closed_7_1_clean`,
with the seven binders listed in the module docstring discharged. -/
theorem closed_7_1_lp
    (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode) (hC : CertifiedReferenceModel ν 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hscale : QuantumConeScalingInput) (hND : LQGMeasureNonDyadicDilationPart)
    (hstd : FrozenConeLogLocalCodeLawStd) (hGBC : FrozenGreenBallCentre)
    (h32 : ClusterOpenLaplacianStmt.{0}) (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0}) (hBdryHB : ClusterBoundaryMeasureZeroStmt.{0})
    (hExistHB : ExistenceHarmonicBallsStmt.{0}) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56HB : UniquenessHarmonicBallsStmt.{0}) (hconf : FrozenHBInitialConfinement)
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0}) (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hlocHB : HarmonicBallLocalSetStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw) (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hrescale : ConeRescaledMeasureIsConeFieldInput) :
    DivSandpileUpperBoundStmt 𝒮 :=
  closed_7_1_clean (𝒮 := 𝒮) (ν := ν) (hC := hC) (hBG := hBG)
    (hexc := frozenBrownianOutwardExcursionAtExit_holds)
    (h0 := h0) (h2 := h2) (hV := hV)
    (hR := ConeMeanZeroRestriction.fpConeMeanZeroRestriction_holds)
    (hscale := hscale) (hND := hND) (hstd := hstd) (hGBC := hGBC)
    (h32 := h32) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat)
    (hBdryHB := hBdryHB) (hExistHB := hExistHB) (hThm11 := hThm11) (hProp56HB := hProp56HB)
    (hconf := hconf) (hI2HB := hI2HB) (hK := hK) (hlocHB := hlocHB) (hE := hE)
    (hFL := hFL) (hE1 := hE1) (hE2 := hE2)
    (hU := frozenUniversalMeasurabilityOfAnalytic_holds)
    (hmeasT := frozenLQGTestIntegralMeasurable_holds)
    (hmin := frozenSuperharmonicMinimumPrinciple_holds)
    (hGB := HBRewire.GreenFunctionBallStmt_of_hb)
    (hpole := HBRewire.FrozenGreenDiscPole_of_hb)
    (hrescale := hrescale)

end MatedCRT

#print axioms MatedCRT.closed_6_1_lp
#print axioms MatedCRT.closed_7_1_lp
