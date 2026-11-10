import MatedCRT.FirstPass.S2g.Corrected24
import MatedCRT.FirstPass.S2g.Canonical
import MatedCRT.FirstPass.S2g.ScaleInvariance
import MatedCRT.FirstPass.S2g.Section6Canonical
import MatedCRT.FirstPass.S2g.HalfBallGate
import MatedCRT.FirstPass.S2i.CanonicalFactor
import MatedCRT.FirstPass.S2i.GlobalFactor

/-! # Corrected Lemmas 2.5, 2.6 and Proposition 6.1: assembly (fp-S2g, q1, round 42)

* `firstPass_6_1_corrected` goes through the canonical Lemma 2.4 `firstPass_2_4_corrected` (`Corrected24.lean`), not through
  the factor step.
* `firstPass_2_5_corrected` and `firstPass_2_6_corrected` apply the z2 factor lemmas `coneCanonicalFactor_proved`
  (`S2i/CanonicalFactor.lean:199`) and `coneGlobalFamilyFactor_proved` (`S2i/GlobalFactor.lean:524`) to the half-ball step
  `coneCanonicalHalfBallStep_of_draft` (`HalfBallGate.lean`). The half-ball step uses no factor step, so there is no cycle.
* Common inputs (all four results): the Draft and frozen inputs of `coneCanonicalHalfBallStep_of_draft`, with
  `FrozenConeLogLocalCodeLawStd` as the frozen interface (operator decision 01:40 UTC); the closure-step inputs of
  `coneHalfBallClosureInsideStep_corrected` (route B, `S2k.lean:38`): `LQGVolumeGrowthAllScalesStmt`,
  `FrozenInsertionCoordinateRule`, `HarmonicBallLocalSetStmt`, `ClusterStrongCompatibilityStmt`, `WholePlaneLQGModelStep`,
  `FrozenConeWholePlaneFieldLaw` (frozen, `Frozen/S2g.lean`); `VolumeGrowthStmt`; for 2.5 and 2.6 also the frozen cone externals `ConeCircleLawUniqueStep`
  and `ConeReferenceExistsStep` (`FirstPass/Frozen/S2i.lean`), and `QuantumConeScalingInput`, `LQGMeasurePropertiesStmt`. -/

open MeasureTheory Set Filter Topology Metric HarmonicBalls

namespace MatedCRT

/-- **Corrected Proposition 6.1 (q1, fp-S2g).** The upper bound from the corrected canonical Lemma 2.4. -/
theorem firstPass_6_1_corrected (𝒮 : SpaceFillingSLEModel) (h610 : IterativeBoundStmt 𝒮)
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
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0}) (hSC : ClusterStrongCompatibilityStmt.{0})
    (hB2 : WholePlaneLQGModelStep) (hFL : FrozenConeWholePlaneFieldLaw)
    (h27 : VolumeGrowthStmt) : IDLAUpperBoundStmt 𝒮 :=
  firstPass_6_1_canonical24 𝒮 h610 h51
    (firstPass_2_4_corrected hU hmeasT hstd hmin hCentre hGB hpole hOpen hSup hCons hMono hCompat hBdry hExist hThm11
      hProp56 hconf hI2 hK hloc hSC hB2 hFL h27)

/-- **Corrected Lemma 2.5, canonical stopped factorization and joint law (q1, fp-S2g).** The factor step
`ConeCanonicalFactorStep` is obtained from the proved lemma `coneCanonicalFactor_proved` (z2) applied to the half-ball step
`coneCanonicalHalfBallStep_of_draft` and the closure step `coneHalfBallClosureInsideStep_corrected`; no factor step is
assumed. -/
theorem firstPass_2_5_corrected
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
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0}) (hSC : ClusterStrongCompatibilityStmt.{0})
    (hB2 : WholePlaneLQGModelStep) (hFL : FrozenConeWholePlaneFieldLaw)
    (h27 : VolumeGrowthStmt)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt) :
    ConeScaleInvarianceUpToFixedTimeCanonicalStmt :=
  firstPass_2_5_canonical_of_factor
    (coneCanonicalFactor_proved
      (coneCanonicalHalfBallStep_of_draft hU hmeasT hstd hmin hCentre hGB hpole hOpen hSup hCons hMono hCompat hBdry
        hExist hThm11 hProp56 hconf)
      (coneHalfBallClosureInsideStep_corrected hI2 hK hloc hExist hSC h27 hB2 hFL) h27 hE1 hE2)
    hscale h22

/-- **Corrected Lemma 2.6, global family scale invariance (q1, fp-S2g).** The global factor step
`ConeGlobalFamilyFactorStep` is obtained from the proved lemma `coneGlobalFamilyFactor_proved` (z2) applied to the half-ball
step `coneCanonicalHalfBallStep_of_draft` and the closure step `coneHalfBallClosureInsideStep_corrected`; no factor step is
assumed. -/
theorem firstPass_2_6_corrected
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
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0}) (hSC : ClusterStrongCompatibilityStmt.{0})
    (hB2 : WholePlaneLQGModelStep) (hFL : FrozenConeWholePlaneFieldLaw)
    (h27 : VolumeGrowthStmt)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt) :
    ConeScaleInvarianceStmt :=
  firstPass_2_6_of_globalFamilyFactor
    (coneGlobalFamilyFactor_proved
      (coneCanonicalHalfBallStep_of_draft hU hmeasT hstd hmin hCentre hGB hpole hOpen hSup hCons hMono hCompat hBdry
        hExist hThm11 hProp56 hconf)
      (coneHalfBallClosureInsideStep_corrected hI2 hK hloc hExist hSC h27 hB2 hFL) h27 hE1 hE2 hscale h22)
    hscale h22

end MatedCRT
