import MatedCRT.Proofs.Sec4.Prop42Closure.PlateauScalingAssembly

/-! # FIRST PASS S2k: the closure route of Proposition 4.2 (task fp-S2k-closure-inside)

Route Z5 (operator ruling 00:29 UTC): written argument `notes/prop42-proof/prop42-proof.tex:230-304` (AUDIT CORRECT). The
assembly is in `Proofs/Sec4/Prop42Closure/PlateauScalingAssembly.lean` and the reduction in `ConePrematureNull.lean`; this
file states the three results in FirstPass form, with their inputs classified.

* `wholePlaneVolumeGrowthAeStep_fp`: `WholePlaneVolumeGrowthAeStep` (B1, `ConeWholePlaneSteps.lean:47`) from the EXTERNAL
  Harmonic-Balls Draft `LQGVolumeGrowthAllScalesStmt` (I2, `HarmonicBalls/Draft/Section2.lean:122`). PROVED-FP.
* `plateauScaleInvarianceStep_fp`: `PlateauScaleInvarianceStep` (fact (1), `HalfBallPlateau.lean:51`) from I2, from the NEW
  input K `DS11CoordinateRuleFixedAffine` (`Proposed/DuplantierSheffieldCoordinate2011.lean:116`) and from the NEW input H
  `ScaledBoundedRepresentativesStep` (`ScaledRegularizedFamily.lean:47`). OPEN.
* `coneHalfBallClosureInsideStep_fp`: `ConeHalfBallClosureInsideStep` (`StoppedClosure.lean:18`) from the inputs of the two
  results above and the EXTERNAL Draft/External inputs `hloc`, `hEx`, `hSC`, `hVG`, `hB2`, `hFL`. OPEN (K and H remain).

The locality input of the half-ball reduction is supplied internally (`LQGMeasureLocalityFunctionalStep_proof`). -/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls TopologicalSpace

/-- **B1 (PROVED-FP).** The whole-plane volume growth at radius `3/4` follows from the all-scales input I2. -/
theorem wholePlaneVolumeGrowthAeStep_fp (hI2 : LQGVolumeGrowthAllScalesStmt.{0}) :
    WholePlaneVolumeGrowthAeStep :=
  wholePlaneVolumeGrowthAeStep_of_allScales hI2

/-- **Fact (1), plateau scale invariance (OPEN).** Conditional on the NEW inputs K (`DS11CoordinateRuleFixedAffine`, the
LQG coordinate rule for fixed affine maps) and H (`ScaledBoundedRepresentativesStep`). -/
theorem plateauScaleInvarianceStep_fp (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hDS : MatedCRT.Proposed.DS11CoordinateRuleFixedAffine) (hrep : ScaledBoundedRepresentativesStep) :
    PlateauScaleInvarianceStep :=
  plateauScaleInvarianceStep_assembled hI2 hDS hrep

/-- **`ConeHalfBallClosureInsideStep` (OPEN).** Route Z5: the plateau fact (1) and B1 feed the half-ball reduction
`coneHalfBallClosureInsideStep_of_fieldLaw`. -/
theorem coneHalfBallClosureInsideStep_fp (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hDS : MatedCRT.Proposed.DS11CoordinateRuleFixedAffine) (hrep : ScaledBoundedRepresentativesStep)
    (hloc : HarmonicBallLocalSetStmt.{0}) (hEx : ExistenceHarmonicBallsStmt.{0})
    (hSC : ClusterStrongCompatibilityStmt.{0}) (hVG : VolumeGrowthStmt)
    (hB2 : WholePlaneLQGModelStep) (hFL : ConeWholePlaneFieldLawStep) :
    ConeHalfBallClosureInsideStep :=
  coneHalfBallClosureInsideStep_of_fieldLaw hloc hEx hSC (plateauScaleInvarianceStep_fp hI2 hDS hrep) hVG
    (wholePlaneVolumeGrowthAeStep_fp hI2) hB2 hFL

end MatedCRT
