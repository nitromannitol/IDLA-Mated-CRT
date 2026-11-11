import MatedCRT.FirstPass.S2g
import MatedCRT.FirstPass.S2g.HalfBallGate
import MatedCRT.FirstPass.S2k
import MatedCRT.FirstPass.Frozen.S4S5b
import MatedCRT.FirstPass.S2m

/-!
# Closure step of the corrected Lemma 2.4, renamed copy

Copy of `coneHalfBallClosureInsideStep_corrected` (`FirstPass/S2g/Corrected24.lean:33`) with the same statement and the same
proof, placed in `MatedCRT.S5r`. Reason: `FirstPass/S2g/Corrected24.lean` and `FirstPass/S2b.lean` both declare
`MatedCRT.firstPass_2_4_corrected` (with different conclusions; the S2g one is firstPass_2_4_canonical), so a module that imports both (for example
`FirstPass/S5q.lean`, which imports `FirstPass/S2b.lean` through `FirstPass/S5m.lean`) cannot import `Corrected24`.
This copy imports the same modules as `Corrected24` except `Corrected24` itself. The original file is not edited.
-/

open MeasureTheory Set Filter Topology Metric HarmonicBalls

namespace MatedCRT.S5r

/-- Copy of `MatedCRT.coneHalfBallClosureInsideStep_corrected` (`FirstPass/S2g/Corrected24.lean:33`): the
`ConeHalfBallClosureInsideStep` from the route-B inputs, via `coneHalfBallClosureInsideStep_fp` (`FirstPass/S2k.lean:38`)
and `firstPass_wholePlaneLQGModel_of_existence` (`FirstPass/S2m.lean:26`). Same inputs as the original. -/
theorem coneHalfBallClosureInsideStep_corrected
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0}) (hEx : ExistenceHarmonicBallsStmt.{0})
    (hSC : ClusterStrongCompatibilityStmt.{0}) (hVG : VolumeGrowthStmt)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion) (hFL : FPConeWholePlaneFieldLaw) :
    ConeHalfBallClosureInsideStep :=
  coneHalfBallClosureInsideStep_fp hI2 hK hloc hEx hSC hVG
    (MatedCRT.FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence hE) hFL

end MatedCRT.S5r
