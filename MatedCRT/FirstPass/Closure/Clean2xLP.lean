import MatedCRT.FirstPass.Closure.HSCRewire
import MatedCRT.FirstPass.Closure.OwnBinderRewire
import MatedCRT.FirstPass.Closure.HSCDerived
import MatedCRT.FirstPass.HBRewire
import MatedCRT.FirstPass.LPBridge.UniversalMeasurability
import MatedCRT.FirstPass.LPBridge.LQGTestIntegralMeasurable
import MatedCRT.FirstPass.LPBridge.MinimumPrinciples

/-!
# Cone harmonic balls and scale invariance, results 2.3 to 2.6, with the LP-bridge binders discharged

Lean forms of the counted rows 2.3, 2.4, 2.5 and 2.6 (`docs/campaign/COUNTED.md`), each with the binders
discharged by existing theorems whose statements are exactly the binder types:

* `closed_2_3_lp` (row 2.3, from `closed_2_3_lit_noSC`, `MatedCRT/FirstPass/Closure/HSCRewire.lean:166`):
  `hU`, `hmeasT`, `hmin` are `frozenUniversalMeasurabilityOfAnalytic_holds`,
  `frozenLQGTestIntegralMeasurable_holds`, `frozenSuperharmonicMinimumPrinciple_holds`
  (`MatedCRT/FirstPass/LPBridge/`); `hGB` is `HBRewire.GreenFunctionBallStmt_of_hb` and `hpole` is
  `HBRewire.FrozenGreenDiscPole_of_hb` (`MatedCRT/FirstPass/HBRewire.lean:33`, `:40`).
* `closed_2_4_lp`, `closed_2_5_lp`, `closed_2_6_lp` (rows 2.4, 2.5, 2.6, from the own-binder wrappers
  `firstPass_2_4_ownBinders`, `firstPass_2_5_ownBinders`, `firstPass_2_6_ownBinders` in
  `MatedCRT/FirstPass/Closure/OwnBinderRewire.lean:133`, `:153`, `:174`): the cluster strong compatibility
  binder `hSC` is `frozenClusterStrongCompatibility_of_volumeGrowth hI2`
  (`MatedCRT/FirstPass/Closure/HSCDerived.lean:19`). No other binder of these rows has a concluder.

The binders `hND` (`LQGMeasureNonDyadicDilationPart`), `hscale`
(`QuantumConeScalingInput`), `hE1`, `hE2`, `hBG` and the Harmonic-Balls Draft statements stay as hypotheses.
Conclusions are unchanged.
-/

namespace MatedCRT
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- **Cone harmonic balls (Theorem 2.3), with the LP-bridge binders discharged.**
The conclusion is `ConeHarmonicBallsStmt`, as for `closed_2_3_lit_noSC`. -/
theorem closed_2_3_lp
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hscale : QuantumConeScalingInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hGBC : FrozenGreenBallCentre)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdryHB : ClusterBoundaryMeasureZeroStmt.{0})
    (hExistHB : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56HB : UniquenessHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hlocHB : HarmonicBallLocalSetStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hrescale : ConeRescaledMeasureIsConeFieldInput) :
    ConeHarmonicBallsStmt :=
  closed_2_3_lit_noSC (hBG := hBG) (hscale := hscale) (hND := hND) (hstd := hstd)
    (hGBC := hGBC) (h32 := h32) (hSup := hSup) (hCons := hCons) (hMono := hMono)
    (hCompat := hCompat) (hBdryHB := hBdryHB) (hExistHB := hExistHB) (hThm11 := hThm11)
    (hProp56HB := hProp56HB) (hconf := hconf) (hI2HB := hI2HB) (hK := hK) (hlocHB := hlocHB)
    (hE := hE) (hFL := hFL) (hE1 := hE1) (hE2 := hE2)
    (hU := frozenUniversalMeasurabilityOfAnalytic_holds)
    (hmeasT := frozenLQGTestIntegralMeasurable_holds)
    (hmin := frozenSuperharmonicMinimumPrinciple_holds)
    (hGB := HBRewire.GreenFunctionBallStmt_of_hb)
    (hpole := HBRewire.FrozenGreenDiscPole_of_hb)
    (hrescale := hrescale)

/-- **Lemma 2.4 (cone harmonic balls up to a fixed time), with the cluster strong compatibility
binder discharged.** The conclusion is `ConeHarmonicBallsUpToFixedTimeCanonicalStmt`, as for
`firstPass_2_4_ownBinders`. -/
theorem closed_2_4_lp
    (hstd : FrozenConeLogLocalCodeLawStd) (hCentre : FrozenGreenBallCentre)
    (hOpen : ClusterOpenLaplacianStmt.{0}) (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0}) (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0}) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0}) (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw) (hBG : FrozenBerestyckiGwynneConeBallMass) :
    ConeHarmonicBallsUpToFixedTimeCanonicalStmt :=
  firstPass_2_4_ownBinders (hstd := hstd) (hCentre := hCentre) (hOpen := hOpen) (hSup := hSup)
    (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hExist := hExist)
    (hThm11 := hThm11) (hProp56 := hProp56) (hconf := hconf) (hI2 := hI2) (hK := hK)
    (hloc := hloc) (hSC := frozenClusterStrongCompatibility_of_volumeGrowth hI2) (hE := hE)
    (hFL := hFL) (hBG := hBG)

/-- **Lemma 2.5 (scale invariance up to a fixed time), with the cluster strong compatibility binder
discharged.** The conclusion is `ConeScaleInvarianceUpToFixedTimeCanonicalStmt`, as for
`firstPass_2_5_ownBinders`. -/
theorem closed_2_5_lp
    (hstd : FrozenConeLogLocalCodeLawStd) (hCentre : FrozenGreenBallCentre)
    (hOpen : ClusterOpenLaplacianStmt.{0}) (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0}) (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0}) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0}) (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw) (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (hND : LQGMeasureNonDyadicDilationPart) :
    ConeScaleInvarianceUpToFixedTimeCanonicalStmt :=
  firstPass_2_5_ownBinders (hstd := hstd) (hCentre := hCentre) (hOpen := hOpen) (hSup := hSup)
    (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hExist := hExist)
    (hThm11 := hThm11) (hProp56 := hProp56) (hconf := hconf) (hI2 := hI2) (hK := hK)
    (hloc := hloc) (hSC := frozenClusterStrongCompatibility_of_volumeGrowth hI2) (hE := hE)
    (hFL := hFL) (hBG := hBG) (hE1 := hE1) (hE2 := hE2) (hscale := hscale) (hND := hND)

/-- **Lemma 2.6 (scale invariance, corrected form), with the cluster strong compatibility binder
discharged.** The conclusion is `ConeScaleInvarianceStmt`, as for `firstPass_2_6_ownBinders`. -/
theorem closed_2_6_lp
    (hstd : FrozenConeLogLocalCodeLawStd) (hCentre : FrozenGreenBallCentre)
    (hOpen : ClusterOpenLaplacianStmt.{0}) (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0}) (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0}) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0}) (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw) (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (hND : LQGMeasureNonDyadicDilationPart) :
    ConeScaleInvarianceStmt :=
  firstPass_2_6_ownBinders (hstd := hstd) (hCentre := hCentre) (hOpen := hOpen) (hSup := hSup)
    (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry) (hExist := hExist)
    (hThm11 := hThm11) (hProp56 := hProp56) (hconf := hconf) (hI2 := hI2) (hK := hK)
    (hloc := hloc) (hSC := frozenClusterStrongCompatibility_of_volumeGrowth hI2) (hE := hE)
    (hFL := hFL) (hBG := hBG) (hE1 := hE1) (hE2 := hE2) (hscale := hscale) (hND := hND)

end MatedCRT

#print axioms MatedCRT.closed_2_3_lp
#print axioms MatedCRT.closed_2_4_lp
#print axioms MatedCRT.closed_2_5_lp
#print axioms MatedCRT.closed_2_6_lp
