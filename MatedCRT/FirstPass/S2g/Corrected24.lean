import MatedCRT.FirstPass.S2g
import MatedCRT.FirstPass.S2g.HalfBallGate

/-! # Corrected Lemma 2.4, canonical stopped family: assembly (fp-S2g, q1, round 41)

`firstPass_2_4_corrected` is the statement `ConeHarmonicBallsUpToFixedTimeCanonicalStmt` (`S2g.lean`, corrected canonical
stopping time `T = halfBallTime`, notes/fp-gaps/CHATGPT-2-4-2-5-statements.md). It is assembled from

* `coneCanonicalHalfBallStep_of_draft` (`HalfBallGate.lean`): the pathwise canonical half-ball existence, from the Draft
  statements and the frozen / interface inputs listed as hypotheses below;
* `firstPass_2_4_canonical_of_steps` (`S2g.lean`): the measurability and uniqueness reduction, which uses the closure
  containment step `ConeHalfBallClosureInsideStep` (NOT in the paper; see its docstring) and `VolumeGrowthStmt`.

The proof is an application; the hypotheses are the exact remaining inputs. -/

open MeasureTheory Set Filter Topology Metric HarmonicBalls

namespace MatedCRT

/-- **Corrected Lemma 2.4 (canonical stopped family, q1, fp-S2g).** The conditional assembly. -/
theorem firstPass_2_4_corrected
    (hU : FrozenUniversalMeasurabilityOfAnalytic) (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hstd : CandidateConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple) (hCentre : FrozenGreenBallCentre)
    (hGB : HarmonicBalls.GreenFunctionBallStmt) (hpole : FrozenGreenDiscPole)
    (hOpen : ClusterOpenLaplacianStmt.{0}) (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0}) (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0}) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hcl : ConeHalfBallClosureInsideStep) (h27 : VolumeGrowthStmt) :
    ConeHarmonicBallsUpToFixedTimeCanonicalStmt :=
  firstPass_2_4_canonical_of_steps
    (coneCanonicalHalfBallStep_of_draft hU hmeasT hstd hmin hCentre hGB hpole hOpen hSup hCons hMono hCompat hBdry
      hExist hThm11 hProp56 hconf)
    hcl h27

end MatedCRT
