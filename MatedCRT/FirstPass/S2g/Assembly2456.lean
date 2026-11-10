import MatedCRT.FirstPass.S2g.Corrected24
import MatedCRT.FirstPass.S2g.Canonical
import MatedCRT.FirstPass.S2g.ScaleInvariance
import MatedCRT.FirstPass.S2g.Section6Canonical

/-! # Corrected Lemmas 2.5, 2.6 and Proposition 6.1: assembly (fp-S2g, q1, round 41)

* `firstPass_6_1_corrected` goes through the canonical Lemma 2.4 `firstPass_2_4_corrected` (`Corrected24.lean`), not through
  the factor step. Its inputs are the 2.4 inputs and `ConeHalfBallClosureInsideStep` (not in the paper) and `VolumeGrowthStmt`.
* `firstPass_2_5_corrected` and `firstPass_2_6_corrected` are the existing factor-step assemblies
  (`firstPass_2_5_canonical_of_factor`, `Canonical.lean`; `firstPass_2_6_of_globalFamilyFactor`, `ScaleInvariance.lean`) with the
  corrected names. Their only NEW hypotheses are the factor steps `ConeCanonicalFactorStep` (`Canonical.lean:32`) and
  `ConeGlobalFamilyFactorStep` (`ScaleInvariance.lean:30`), owned by z2 and kept as hypotheses (not derived from the half-ball
  gate, to avoid the cycle). -/

open MeasureTheory Set Filter Topology Metric HarmonicBalls

namespace MatedCRT

/-- **Corrected Proposition 6.1 (q1, fp-S2g).** The upper bound from the corrected canonical Lemma 2.4. -/
theorem firstPass_6_1_corrected (𝒮 : SpaceFillingSLEModel) (h610 : IterativeBoundStmt 𝒮)
    (h51 : IDLALowerBoundStmt 𝒮)
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
    (hcl : ConeHalfBallClosureInsideStep) (h27 : VolumeGrowthStmt) : IDLAUpperBoundStmt 𝒮 :=
  firstPass_6_1_canonical24 𝒮 h610 h51
    (firstPass_2_4_corrected hU hmeasT hstd hmin hCentre hGB hpole hOpen hSup hCons hMono hCompat hBdry hExist hThm11
      hProp56 hconf hcl h27)

/-- **Corrected Lemma 2.5, canonical stopped factorization and joint law (q1, fp-S2g).** Conditional on the factor step
`ConeCanonicalFactorStep` (z2, OPEN; not derived from the half-ball gate). -/
theorem firstPass_2_5_corrected (hfac : ConeCanonicalFactorStep) (hscale : QuantumConeScalingInput)
    (h22 : LQGMeasurePropertiesStmt) : ConeScaleInvarianceUpToFixedTimeCanonicalStmt :=
  firstPass_2_5_canonical_of_factor hfac hscale h22

/-- **Corrected Lemma 2.6, global family scale invariance (q1, fp-S2g).** Conditional on the global factor step
`ConeGlobalFamilyFactorStep` (z2, OPEN). -/
theorem firstPass_2_6_corrected (hfac : ConeGlobalFamilyFactorStep) (hscale : QuantumConeScalingInput)
    (h22 : LQGMeasurePropertiesStmt) : ConeScaleInvarianceStmt :=
  firstPass_2_6_of_globalFamilyFactor hfac hscale h22

end MatedCRT
