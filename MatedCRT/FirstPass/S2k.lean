import MatedCRT.Proofs.Sec4.Prop42Closure.PlateauScalingAssembly
import MatedCRT.FirstPass.S2k.PlateauHBFree
import MatedCRT.FirstPass.Frozen.S2k

/-! # FIRST PASS S2k: the closure route of Proposition 4.2 (task fp-S2k-closure-inside)

* `wholePlaneVolumeGrowthAeStep_fp`: `WholePlaneVolumeGrowthAeStep` (B1, `ConeWholePlaneSteps.lean:47`) from the EXTERNAL
  Harmonic-Balls Draft `LQGVolumeGrowthAllScalesStmt` (I2, `HarmonicBalls/Draft/Section2.lean:122`). PROVED-FP.
* `plateauScaleInvarianceStep_fp`: `PlateauScaleInvarianceStep` (fact (1), `HalfBallPlateau.lean:51`) from I2 and the
  frozen coordinate rule `FrozenInsertionCoordinateRule` (input K, `FirstPass/Frozen/S2k.lean`, TRUE as typed, truth note §1). The
  bounded-representative input H is not used: `FirstPass/S2k/PlateauHBFree.lean` (cycle note section 4.1). PROVED-FP
  conditional on K.
* `coneHalfBallClosureInsideStep_fp`: `ConeHalfBallClosureInsideStep` (`StoppedClosure.lean:18`) from the fact (1) above
  and the EXTERNAL Draft/External inputs `hloc`, `hEx`, `hSC`, `hVG`, `hB2`, `hFL` through the existing reduction
  `coneHalfBallClosureInsideStep_of_fieldLaw` (`ConePrematureNull.lean`).

The locality input of the half-ball reduction is supplied internally (`LQGMeasureLocalityFunctionalStep_proof`). -/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls TopologicalSpace

/-- **B1 (PROVED-FP).** The whole-plane volume growth at radius `3/4` follows from the all-scales input I2. -/
theorem wholePlaneVolumeGrowthAeStep_fp (hI2 : LQGVolumeGrowthAllScalesStmt.{0}) :
    WholePlaneVolumeGrowthAeStep :=
  wholePlaneVolumeGrowthAeStep_of_allScales hI2

/-- **Fact (1), plateau scale invariance (PROVED-FP, H-free).** Conditional on I2 and on the frozen coordinate rule
`FrozenInsertionCoordinateRule` (input K, TRUE as typed). The bounded-representative input H is not used
(`PlateauHBFree.lean`, cycle note section 4.1). -/
theorem plateauScaleInvarianceStep_fp (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule) : PlateauScaleInvarianceStep :=
  MatedCRT.FirstPass.S2k.plateauScaleInvarianceStep_HBfree hI2 (insertionLQGScalingLawStep_of_coordinateRule hK)

/-- **`ConeHalfBallClosureInsideStep` (conditional on the Harmonic-Balls inputs).** The plateau fact (1) (H-free) and B1
feed the half-ball reduction `coneHalfBallClosureInsideStep_of_fieldLaw`. Operator decision pending between this
reduction and the cycle route section 4.2 (see `notes/z2.md`). -/
theorem coneHalfBallClosureInsideStep_fp (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0}) (hEx : ExistenceHarmonicBallsStmt.{0})
    (hSC : ClusterStrongCompatibilityStmt.{0}) (hVG : VolumeGrowthStmt)
    (hB2 : WholePlaneLQGModelStep) (hFL : ConeWholePlaneFieldLawStep) :
    ConeHalfBallClosureInsideStep :=
  coneHalfBallClosureInsideStep_of_fieldLaw hloc hEx hSC (plateauScaleInvarianceStep_fp hI2 hK) hVG
    (wholePlaneVolumeGrowthAeStep_fp hI2) hB2 hFL

end MatedCRT
