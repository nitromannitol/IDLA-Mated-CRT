import MatedCRT.FirstPass.S2k
import MatedCRT.FirstPass.S2g.Corrected24
import MatedCRT.FirstPass.S2g.Assembly2456
import MatedCRT.FirstPass.S2VG.Literature

/-! # FIRST PASS S2VG, Wrappers: hI2 replaced by the literature inputs (task fp-S2-hI2-literature-2)

Each wrapper is a counted declaration with `hI2 : LQGVolumeGrowthAllScalesStmt.{0}` removed. The five cited inputs
`hDGlit`, `hCClit`, `hWlit`, `hElit`, `hNlit` (types `LitWholePlaneBallMass`, `LitCoordChange`, `LitWeylScaling`,
`LitExistence`, `LitNonatomic`; `S2VG/Literature.lean`) are hypotheses of the wrapper and are passed to
`lqgVolumeGrowthAllScalesStmt_litI2`, which gives I2. The conclusion and every other hypothesis are those of the original
declaration. No Draft or frozen statement is changed.

Counted declarations wrapped: `S2k.lean:24` (`wholePlaneVolumeGrowthAeStep_fp`), `S2k.lean:31` (`plateauScaleInvarianceStep_fp`),
`S2k.lean:38` (`coneHalfBallClosureInsideStep_fp`), `S2g/Corrected24.lean:44` (`firstPass_2_4_canonical`),
`S2g/Assembly2456.lean:56` (`firstPass_2_5_canonical`), `S2g/Assembly2456.lean:115` (`firstPass_2_6_law_corrected`),
`S2g/Assembly2456.lean:31` (`firstPass_6_1_corrected`). -/

open MeasureTheory HarmonicBalls
open MatedCRT.S2VG

namespace MatedCRT

/-- B1 (`wholePlaneVolumeGrowthAeStep_fp`, `S2k.lean:24`) with hI2 from the literature inputs (cited, class b: `LitWholePlaneBallMass`, `LitCoordChange`, `LitWeylScaling`, `LitExistence`, `LitNonatomic`; Literature.lean). -/
theorem wholePlaneVolumeGrowthAeStep_litI2
    (hDGlit : LitWholePlaneBallMass) (hCClit : LitCoordChange) (hWlit : LitWeylScaling)
    (hElit : LitExistence) (hNlit : LitNonatomic) : WholePlaneVolumeGrowthAeStep :=
  MatedCRT.wholePlaneVolumeGrowthAeStep_fp (S2VG.lqgVolumeGrowthAllScalesStmt_litI2 hDGlit hCClit hWlit hElit hNlit)

/-- Fact (1), plateau scale invariance (`plateauScaleInvarianceStep_fp`, `S2k.lean:31`) with hI2 from the literature inputs (cited, class b: `LitWholePlaneBallMass`, `LitCoordChange`, `LitWeylScaling`, `LitExistence`, `LitNonatomic`; Literature.lean). -/
theorem plateauScaleInvarianceStep_litI2
    (hDGlit : LitWholePlaneBallMass) (hCClit : LitCoordChange) (hWlit : LitWeylScaling)
    (hElit : LitExistence) (hNlit : LitNonatomic)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule) : PlateauScaleInvarianceStep :=
  MatedCRT.plateauScaleInvarianceStep_fp (S2VG.lqgVolumeGrowthAllScalesStmt_litI2 hDGlit hCClit hWlit hElit hNlit) hK

/-- `ConeHalfBallClosureInsideStep` (`coneHalfBallClosureInsideStep_fp`, `S2k.lean:38`) with hI2 from the literature inputs (cited, class b: `LitWholePlaneBallMass`, `LitCoordChange`, `LitWeylScaling`, `LitExistence`, `LitNonatomic`; Literature.lean). -/
theorem coneHalfBallClosureInsideStep_litI2
    (hDGlit : LitWholePlaneBallMass) (hCClit : LitCoordChange) (hWlit : LitWeylScaling)
    (hElit : LitExistence) (hNlit : LitNonatomic)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0}) (hEx : ExistenceHarmonicBallsStmt.{0})
    (hSC : ClusterStrongCompatibilityStmt.{0}) (hVG : VolumeGrowthStmt)
    (hB2 : WholePlaneLQGModelStep) (hFL : ConeWholePlaneFieldLawStep) :
    ConeHalfBallClosureInsideStep :=
  MatedCRT.coneHalfBallClosureInsideStep_fp (S2VG.lqgVolumeGrowthAllScalesStmt_litI2 hDGlit hCClit hWlit hElit hNlit)
    hK hloc hEx hSC hVG hB2 hFL

/-- **Lemma 2.4 (counted: `firstPass_2_4_canonical`, `Corrected24.lean:44`) with hI2 from the literature inputs (cited, class b: `LitWholePlaneBallMass`, `LitCoordChange`, `LitWeylScaling`, `LitExistence`, `LitNonatomic`; Literature.lean).** -/
theorem firstPass_2_4_canonical_litI2
    (hU : FrozenUniversalMeasurabilityOfAnalytic) (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple) (hCentre : FrozenGreenBallCentre)
    (hGB : HarmonicBalls.GreenFunctionBallStmt) (hpole : FrozenGreenDiscPole)
    (hOpen : ClusterOpenLaplacianStmt.{0}) (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0}) (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0}) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hDGlit : LitWholePlaneBallMass) (hCClit : LitCoordChange) (hWlit : LitWeylScaling)
    (hElit : LitExistence) (hNlit : LitNonatomic)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0}) (hSC : ClusterStrongCompatibilityStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion) (hFL : FPConeWholePlaneFieldLaw)
    (h27 : VolumeGrowthStmt) :
    ConeHarmonicBallsUpToFixedTimeCanonicalStmt :=
  MatedCRT.firstPass_2_4_canonical hU hmeasT hstd hmin hCentre hGB hpole hOpen hSup hCons hMono hCompat hBdry
    hExist hThm11 hProp56 hconf (S2VG.lqgVolumeGrowthAllScalesStmt_litI2 hDGlit hCClit hWlit hElit hNlit)
    hK hloc hSC hE hFL h27

/-- **Lemma 2.5 (counted: `firstPass_2_5_canonical`, `Assembly2456.lean:56`) with hI2 from the literature inputs (cited, class b: `LitWholePlaneBallMass`, `LitCoordChange`, `LitWeylScaling`, `LitExistence`, `LitNonatomic`; Literature.lean).** -/
theorem firstPass_2_5_canonical_litI2
    (hU : FrozenUniversalMeasurabilityOfAnalytic) (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple) (hCentre : FrozenGreenBallCentre)
    (hGB : HarmonicBalls.GreenFunctionBallStmt) (hpole : FrozenGreenDiscPole)
    (hOpen : ClusterOpenLaplacianStmt.{0}) (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0}) (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0}) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hDGlit : LitWholePlaneBallMass) (hCClit : LitCoordChange) (hWlit : LitWeylScaling)
    (hElit : LitExistence) (hNlit : LitNonatomic)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0}) (hSC : ClusterStrongCompatibilityStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion) (hFL : FPConeWholePlaneFieldLaw)
    (h27 : VolumeGrowthStmt)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt) :
    ConeScaleInvarianceUpToFixedTimeCanonicalStmt :=
  MatedCRT.firstPass_2_5_canonical hU hmeasT hstd hmin hCentre hGB hpole hOpen hSup hCons hMono hCompat hBdry
    hExist hThm11 hProp56 hconf (S2VG.lqgVolumeGrowthAllScalesStmt_litI2 hDGlit hCClit hWlit hElit hNlit)
    hK hloc hSC hE hFL h27 hE1 hE2 hscale h22

/-- **Lemma 2.6 (counted: `firstPass_2_6_law_corrected`, `Assembly2456.lean:115`) with hI2 from the literature inputs (cited, class b: `LitWholePlaneBallMass`, `LitCoordChange`, `LitWeylScaling`, `LitExistence`, `LitNonatomic`; Literature.lean).** -/
theorem firstPass_2_6_law_corrected_litI2
    (hU : FrozenUniversalMeasurabilityOfAnalytic) (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple) (hCentre : FrozenGreenBallCentre)
    (hGB : HarmonicBalls.GreenFunctionBallStmt) (hpole : FrozenGreenDiscPole)
    (hOpen : ClusterOpenLaplacianStmt.{0}) (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0}) (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0}) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hDGlit : LitWholePlaneBallMass) (hCClit : LitCoordChange) (hWlit : LitWeylScaling)
    (hElit : LitExistence) (hNlit : LitNonatomic)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0}) (hSC : ClusterStrongCompatibilityStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion) (hFL : FPConeWholePlaneFieldLaw)
    (h27 : VolumeGrowthStmt)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt) :
    ConeScaleInvarianceAEStmt :=
  MatedCRT.firstPass_2_6_law_corrected hU hmeasT hstd hmin hCentre hGB hpole hOpen hSup hCons hMono hCompat hBdry
    hExist hThm11 hProp56 hconf (S2VG.lqgVolumeGrowthAllScalesStmt_litI2 hDGlit hCClit hWlit hElit hNlit)
    hK hloc hSC hE hFL h27 hE1 hE2 hscale h22

/-- **Proposition 6.1 (counted: `firstPass_6_1_corrected`, `Assembly2456.lean:31`) with hI2 from the literature inputs (cited, class b: `LitWholePlaneBallMass`, `LitCoordChange`, `LitWeylScaling`, `LitExistence`, `LitNonatomic`; Literature.lean).** -/
theorem firstPass_6_1_corrected_litI2 (𝒮 : SpaceFillingSLEModel) (h610 : IterativeBoundStmt 𝒮)
    (h51 : IDLALowerBoundStmt 𝒮)
    (hU : FrozenUniversalMeasurabilityOfAnalytic) (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple) (hCentre : FrozenGreenBallCentre)
    (hGB : HarmonicBalls.GreenFunctionBallStmt) (hpole : FrozenGreenDiscPole)
    (hOpen : ClusterOpenLaplacianStmt.{0}) (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0}) (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0}) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hDGlit : LitWholePlaneBallMass) (hCClit : LitCoordChange) (hWlit : LitWeylScaling)
    (hElit : LitExistence) (hNlit : LitNonatomic)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0}) (hSC : ClusterStrongCompatibilityStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion) (hFL : FPConeWholePlaneFieldLaw)
    (h27 : VolumeGrowthStmt) : IDLAUpperBoundStmt 𝒮 :=
  MatedCRT.firstPass_6_1_corrected 𝒮 h610 h51 hU hmeasT hstd hmin hCentre hGB hpole hOpen hSup hCons hMono hCompat
    hBdry hExist hThm11 hProp56 hconf (S2VG.lqgVolumeGrowthAllScalesStmt_litI2 hDGlit hCClit hWlit hElit hNlit)
    hK hloc hSC hE hFL h27

end MatedCRT
