import MatedCRT.FirstPass.S2g.CanonicalGate
import MatedCRT.FirstPass.S2g.SourcePathwise

/-! # The canonical half-ball gate with the source pathwise step discharged

`coneCanonicalHalfBallStep_of_inputs` (`CanonicalGate.lean`) takes the pathwise source step `SourceHalfBallPathwiseStep` as an
input. It is discharged here from the Draft statements (`sourceHalfBallPathwiseStep_of_draft`, `SourcePathwise.lean`). The
remaining inputs are the frozen measurability inputs, the candidate standard-Borel moment law and the frozen potential-theory
inputs. -/

open MeasureTheory Set Filter Topology Metric HarmonicBalls

namespace MatedCRT

/-- **`ConeCanonicalHalfBallStep` from the Draft statements and the remaining inputs.** -/
theorem coneCanonicalHalfBallStep_of_draft (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hmeasT : FrozenLQGTestIntegralMeasurable) (hstd : CandidateConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple) (hC : FrozenGreenBallCentre)
    (hGB : HarmonicBalls.GreenFunctionBallStmt) (hpole : FrozenGreenDiscPole)
    (hOpen : ClusterOpenLaplacianStmt.{0}) (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0}) (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0}) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement) : ConeCanonicalHalfBallStep :=
  coneCanonicalHalfBallStep_of_inputs hU hmeasT
    (sourceHalfBallPathwiseStep_of_draft hOpen hSup hCons hMono hCompat hBdry hExist hThm11 hProp56 hconf)
    hstd hmin hC hGB hpole

end MatedCRT
