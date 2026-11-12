import MatedCRT.FirstPass.Derived.ConeBallMassFromVolumeGrowth
import MatedCRT.FirstPass.Derived.HBInitialConfinement
import MatedCRT.FirstPass.Frozen.S5Cited
import HarmonicBalls.FirstPass.Phase2.BallMassBoundsHolds
import HarmonicBalls.FirstPass.Phase2.CampbellCountedForms
import HarmonicBalls.FirstPass.Phase2.DerivedInputs29
import HarmonicBalls.FirstPass.Phase2.CoordChangeZeroHolds
import HarmonicBalls.FirstPass.Phase2.LQGMeasureExistenceDerived

/-!
# Inputs of the IDLA paper that follow from the Ding-Gwynne ball-mass bounds

The Ding-Gwynne bounds on the LQG mass of Euclidean balls (arXiv:1807.01072, Lemma 3.8) hold for every `γ` and every
model of the whole-plane GFF: `HarmonicBalls.wholePlaneLQGBallMassBounds_holds`. With them, the following inputs of
the IDLA paper, which are cited from Berestycki-Gwynne (Lemma A.1) and from the harmonic-balls paper
of Bou-Rabee and Gwynne (arXiv:2208.11795), are theorems without hypotheses (Type 0 models):

* `frozenLQGVolumeGrowthAllScales_holds`: the volume growth `r^{β⁻} ≤ μ_h(B_r(z)) ≤ r^{β⁺}` at all small scales (I2);
* `frozenBerestyckiGwynneConeBallMass_holds`: the ball masses of the γ-quantum cone;
* `frozenHBInitialConfinement_holds`: the initial compact confinement of the whole-plane clusters;
* `frozenTypicalPointManyGoodScales_holds`: Lemma 8.2 of the harmonic-balls paper;
* `frozenClusterBoundaryMeasureZero_holds`: Proposition 5.3 of the harmonic-balls paper;
* `existenceHarmonicBallsStmt_holds`: Proposition 5.5 of the harmonic-balls paper;
* `harmonicBallLocalSetStmt_holds`: Proposition 1.3 of the harmonic-balls paper.
-/

namespace MatedCRT.FirstPass.Derived

/-- The volume growth of the LQG measure at all small scales (the input I2 of the harmonic-balls paper), from the
Ding-Gwynne ball-mass bounds, the coordinate change of the LQG measure and its existence. -/
theorem frozenLQGVolumeGrowthAllScales_holds : FrozenLQGVolumeGrowthAllScales :=
  HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_rows123.{0}
    HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{0}
    HarmonicBalls.lqgMeasureCoordChange_zero_holds.{0}
    HarmonicBalls.lqgMeasureExistence_forall_field.{0}

/-- The ball masses of the γ-quantum cone (Berestycki-Gwynne, Lemma A.1, eq. (A.1)). -/
theorem frozenBerestyckiGwynneConeBallMass_holds : FrozenBerestyckiGwynneConeBallMass :=
  frozenBerestyckiGwynneConeBallMass_of_ballMassBounds HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{0}

/-- The initial compact confinement of the whole-plane clusters. -/
theorem frozenHBInitialConfinement_holds : FrozenHBInitialConfinement :=
  frozenHBInitialConfinement_of_ballMassBounds HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{0}
    frozenLQGVolumeGrowthAllScales_holds

/-- Lemma 8.2 of the harmonic-balls paper: a typical point of `μ_h` has many good scales. -/
theorem frozenTypicalPointManyGoodScales_holds : FrozenTypicalPointManyGoodScales :=
  HarmonicBalls.firstPass_8_2_S8d_noWeyl_derivedInputsCampbell.{0}
    (hDG := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{0})

/-- Proposition 5.3 of the harmonic-balls paper: the boundary of a cluster has `μ_h`-measure zero. -/
theorem frozenClusterBoundaryMeasureZero_holds : FrozenClusterBoundaryMeasureZero :=
  HarmonicBalls.Closure.closure_5_3_derivedInputsCampbell.{0}
    (hDG := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{0})

/-- Proposition 5.5 of the harmonic-balls paper: existence of harmonic balls. -/
theorem existenceHarmonicBallsStmt_holds : HarmonicBalls.ExistenceHarmonicBallsStmt.{0} :=
  HarmonicBalls.Closure.closure_5_5_derivedInputsCampbell.{0}
    (hDG := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{0})

/-- Proposition 1.3 of the harmonic-balls paper: harmonic balls are local sets. -/
theorem harmonicBallLocalSetStmt_holds : HarmonicBalls.HarmonicBallLocalSetStmt.{0} :=
  HarmonicBalls.Closure.closure_1_3_derivedInputsCampbell.{0}
    (hDG := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{0})

end MatedCRT.FirstPass.Derived
