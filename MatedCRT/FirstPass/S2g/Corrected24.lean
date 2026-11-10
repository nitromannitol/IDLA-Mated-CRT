import MatedCRT.FirstPass.S2g
import MatedCRT.FirstPass.S2g.HalfBallGate
import MatedCRT.FirstPass.S2k

/-! # Corrected Lemma 2.4, canonical stopped family: assembly (fp-S2g, q1, round 42)

`firstPass_2_4_corrected` is the statement `ConeHarmonicBallsUpToFixedTimeCanonicalStmt` (`S2g.lean`, corrected canonical
stopping time `T = halfBallTime`, notes/fp-gaps/CHATGPT-2-4-2-5-statements.md). It is assembled from

* `coneCanonicalHalfBallStep_of_draft` (`HalfBallGate.lean`): the pathwise canonical half-ball existence, from the Draft
  statements and the frozen interface `FrozenConeLogLocalCodeLawStd` (operator decision 01:40 UTC);
* `coneHalfBallClosureInsideStep_corrected` (this file): the closure containment step `ConeHalfBallClosureInsideStep`
  through the route-B reduction `coneHalfBallClosureInsideStep_fp` (`FirstPass/S2k.lean:38`);
* `firstPass_2_4_canonical_of_steps` (`S2g.lean`): the measurability and uniqueness reduction, which uses the closure step
  and `VolumeGrowthStmt`.

The proof is an application; the hypotheses are the exact remaining inputs. The N1-N3 items of the earlier report
(`RadiusThreeQuartersBoundaryNull`, clauses of `ConePathwiseHalfBallInputs`) are not hypotheses of
`coneCanonicalHalfBallStep_of_draft`, so they are moot for this assembly. -/

open MeasureTheory Set Filter Topology Metric HarmonicBalls

namespace MatedCRT

/-- **`ConeHalfBallClosureInsideStep` from the route-B inputs (q1, fp-S2g).** The whole-plane volume growth (B1) and the
plateau scale invariance (fact (1)) are proved inside `coneHalfBallClosureInsideStep_fp` from `hI2` and the frozen coordinate
rule `hK`. The remaining inputs are `hloc`, `hEx`, `hSC`, the volume growth `hVG` (`VolumeGrowthStmt`), and the two NEW
steps `hB2` (`WholePlaneLQGModelStep`) and `hFL` (`ConeWholePlaneFieldLawStep`, frozen as `FrozenConeWholePlaneFieldLaw`
in `Frozen/S2g.lean`). -/
theorem coneHalfBallClosureInsideStep_corrected
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0}) (hEx : ExistenceHarmonicBallsStmt.{0})
    (hSC : ClusterStrongCompatibilityStmt.{0}) (hVG : VolumeGrowthStmt)
    (hB2 : WholePlaneLQGModelStep) (hFL : FrozenConeWholePlaneFieldLaw) :
    ConeHalfBallClosureInsideStep :=
  coneHalfBallClosureInsideStep_fp hI2 hK hloc hEx hSC hVG hB2 hFL

/-- **Corrected Lemma 2.4 (canonical stopped family, q1, fp-S2g).** The conditional assembly. -/
theorem firstPass_2_4_corrected
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
    (h27 : VolumeGrowthStmt) :
    ConeHarmonicBallsUpToFixedTimeCanonicalStmt :=
  firstPass_2_4_canonical_of_steps
    (coneCanonicalHalfBallStep_of_draft hU hmeasT hstd hmin hCentre hGB hpole hOpen hSup hCons hMono hCompat hBdry
      hExist hThm11 hProp56 hconf)
    (coneHalfBallClosureInsideStep_corrected hI2 hK hloc hExist hSC h27 hB2 hFL) h27

end MatedCRT
