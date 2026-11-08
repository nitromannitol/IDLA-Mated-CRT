import MatedCRT.Proofs.Sec4.Prop42Closure.PlateauCanonicalLaw
import MatedCRT.Proofs.Sec4.Prop42Closure.InsertionScalingLaw
import MatedCRT.Proofs.Sec4.Prop42Closure.ScaledRegularizedFamily
import MatedCRT.Proofs.Sec4.Prop42Closure.ConePrematureNull
import MatedCRT.Proposed.DuplantierSheffieldCoordinate2011

/-! # Plateau scale invariance and the cone half-ball closure: the final consumer (Proposition 4.2, z5)

Task `z5-plateau-scaling-final-consumer`. Written argument: `notes/prop42-proof/prop42-proof.tex`, lines 245-268.

`plateauScaleInvarianceStep_assembled` proves `PlateauScaleInvarianceStep` (`HalfBallPlateau.lean:51`) from three
hypotheses, each a `Prop` in full:
* `hI2 : LQGVolumeGrowthAllScalesStmt.{0}`: the Harmonic-Balls input I2 (`HarmonicBalls/Draft/Section2.lean:122`), the
  volume growth of every whole-plane LQG measure on every ball. Retained; not proved here.
* `hDS : MatedCRT.Proposed.DS11CoordinateRuleFixedAffine`: input K, the LQG coordinate rule for the fixed affine maps at
  all real scales (`WPN-42-insertion-coordinate-extension`, `docs/campaign/GAPS-TAKEOVER-20261108.md`). The field law and
  the Borel recovery of the insertion measure are proved in `InsertionScalingLaw.lean`; the coordinate rule is not.
* `hrep : ScaledBoundedRepresentativesStep`: input H, bounded subharmonic representatives of the dilated measure, for every
  measure (`WPN-42-scaled-representatives`, `ScaledRegularizedFamily.lean:43`). The deterministic scaling of the regularized
  family is proved from it (`scaledRegularizedFamilyStep_of_representatives`).

`coneHalfBallClosureInsideStep_assembled` feeds this statement to the half-ball/plateau reduction
`coneHalfBallClosureInsideStep_of_inputs` (`ConePrematureNull.lean:183`), where `PlateauScaleInvarianceStep` is the input
`hfact1`. The other inputs of the reduction are carried explicitly:
* locality: `hLoc : LQGMeasureLocalityFunctionalStep` (`WPN-42-locality`, `LQGMeasureFunctional.lean:42`);
* cone transfer: `hFL : ConeWholePlaneFieldLawStep`, `hB2 : WholePlaneLQGModelStep`, `hVG : VolumeGrowthStmt` (IDLA Lemma 2.7);
* the Harmonic-Balls inputs `hloc`, `hEx`, `hSC` of the reduction.
The whole-plane volume growth input `WholePlaneVolumeGrowthAeStep` (B1) is not a further input: it follows from I2
(`wholePlaneVolumeGrowthAeStep_of_allScales`).

Strict growth is not an input here. `HarmonicBallStrictObstacleGapStep` (`DivSandpileLowerBound/Final.lean:32`) is the
fixed-time strict obstacle gap of the Proposition 4.2 chain (`Prop42Closure/Assembly.lean`). It is open, it is not an input
of the cone-closure reduction, and this file neither proves nor assumes it. Nothing here states Proposition 4.2 as closed. -/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls ProbabilityTheory
open scoped Pointwise ENNReal

/-- **B1 from I2.** The whole-plane LQG measure of insertion `γ` has `γ < lqgQ γ` (`self_lt_lqgQ`), so the all-scales
input I2 gives volume growth on every ball, in particular on `B_{3/4}`, almost surely. -/
theorem wholePlaneVolumeGrowthAeStep_of_allScales (hI2 : LQGVolumeGrowthAllScalesStmt.{0}) :
    WholePlaneVolumeGrowthAeStep := by
  intro γ hγ hγ2 Ω _ P _ _ _ μ hGFF hμ
  obtain ⟨βm, βp, hvg⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 (self_lt_lqgQ hγ hγ2) hGFF hμ
  exact hvg.mono fun ω hω => ⟨βm, βp, hω.2 (3 / 4) (by norm_num)⟩

/-- **`PlateauScaleInvarianceStep`, from the named inputs I2, K and H.** Input K gives the scaled measure with `μ'' =_d μ`
and the random constant `c > 0` (`insertionLQGScalingLawStep_of_coordinateRule`); input H gives the dilated regularized
family for `μ''` (`scaledRegularizedFamilyStep_of_representatives`); `plateauScaleInvarianceStep_of_canonical` then gives
`P[r ∈ P] = P[a r ∈ P]` for all `a, r > 0` and all whole-plane data. -/
theorem plateauScaleInvarianceStep_assembled (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hDS : MatedCRT.Proposed.DS11CoordinateRuleFixedAffine) (hrep : ScaledBoundedRepresentativesStep) :
    PlateauScaleInvarianceStep :=
  plateauScaleInvarianceStep_of_canonical hI2 (insertionLQGScalingLawStep_of_coordinateRule hDS)
    (scaledRegularizedFamilyStep_of_representatives hrep)

/-- **`ConeHalfBallClosureInsideStep`, through the half-ball/plateau reduction.** The plateau statement
`plateauScaleInvarianceStep_assembled` is fed to `coneHalfBallClosureInsideStep_of_inputs` as `hfact1`, with B1 supplied by
`wholePlaneVolumeGrowthAeStep_of_allScales hI2`. The residual hypotheses are those listed in the module docstring. -/
theorem coneHalfBallClosureInsideStep_assembled (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hDS : MatedCRT.Proposed.DS11CoordinateRuleFixedAffine) (hrep : ScaledBoundedRepresentativesStep)
    (hloc : HarmonicBallLocalSetStmt.{0}) (hEx : ExistenceHarmonicBallsStmt.{0})
    (hSC : ClusterStrongCompatibilityStmt.{0}) (hVG : VolumeGrowthStmt)
    (hB2 : WholePlaneLQGModelStep) (hFL : ConeWholePlaneFieldLawStep)
    (hLoc : LQGMeasureLocalityFunctionalStep) : ConeHalfBallClosureInsideStep :=
  coneHalfBallClosureInsideStep_of_inputs hloc hEx hSC (plateauScaleInvarianceStep_assembled hI2 hDS hrep) hVG
    (wholePlaneVolumeGrowthAeStep_of_allScales hI2) hB2 hFL hLoc

end MatedCRT
