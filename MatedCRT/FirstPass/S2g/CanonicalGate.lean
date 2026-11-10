import MatedCRT.FirstPass.S2g.MomentSeparation

/-!
# The canonical half-ball gate, from its inputs (q1, fp-S2g)

The open gate `ConeCanonicalHalfBallStep` (`S2g.lean`) is reduced, deterministically, to the inputs of the good-set
route: the frozen measurability inputs `FrozenUniversalMeasurabilityOfAnalytic` and `FrozenLQGTestIntegralMeasurable`,
the NEW pathwise statement `SourceHalfBallPathwiseStep` (open), the candidate standard-Borel moment law
`CandidateConeLogLocalCodeLawStd` (not frozen), and the frozen potential-theory inputs of `coneCanonicalHalfBallStep_of_good`.
The countable separation input `CandidateMomentSeparation` is discharged (`S2g/MomentSeparation.lean`).

Terminology: quantum cone and LQG measure (Duplantier-Miller-Sheffield), harmonic balls (Armstrong-Kuusi-Mourrat), Green
functions and obstacle problem (Armitage-Gardiner).
-/

namespace MatedCRT

/-- **Canonical half-ball gate from its inputs (q1, fp-S2g).** `ConeCanonicalHalfBallStep` follows from the good-set route. -/
theorem coneCanonicalHalfBallStep_of_inputs (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hsrc : SourceHalfBallPathwiseStep) (hstd : CandidateConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple) (hC : FrozenGreenBallCentre)
    (hGB : HarmonicBalls.GreenFunctionBallStmt) (hpole : FrozenGreenDiscPole) :
    ConeCanonicalHalfBallStep :=
  coneCanonicalHalfBallStep_of_good (coneHalfBallGood_of_source_sep hU hmeasT hsrc hstd) hmin hC hGB hpole

/-- **Corrected Lemma 2.4, canonical form, from the good-set inputs (q1, fp-S2g).** The canonical statement
`ConeHarmonicBallsUpToFixedTimeCanonicalStmt` follows from the inputs of `coneCanonicalHalfBallStep_of_inputs` together
with the closure containment step and the volume growth statement used by `firstPass_2_4_canonical_of_steps`. -/
theorem firstPass_2_4_canonical_of_inputs (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hsrc : SourceHalfBallPathwiseStep) (hstd : CandidateConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple) (hC : FrozenGreenBallCentre)
    (hGB : HarmonicBalls.GreenFunctionBallStmt) (hpole : FrozenGreenDiscPole)
    (hcl : ConeHalfBallClosureInsideStep) (h27 : VolumeGrowthStmt) :
    ConeHarmonicBallsUpToFixedTimeCanonicalStmt :=
  firstPass_2_4_canonical_of_steps
    (coneCanonicalHalfBallStep_of_inputs hU hmeasT hsrc hstd hmin hC hGB hpole) hcl h27

end MatedCRT
