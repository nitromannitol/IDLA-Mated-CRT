import MatedCRT.Proofs.Sec2.ConeHarmonicBallsUpToFixedTime.WholePlane
import MatedCRT.Proofs.Measurability.ConeScaleInputs

/-!
# Lemma 2.4 and Theorem 2.3 with the whole-plane step proved from HB22

* `coneHarmonicBallsUpToFixedTime_of_hb`: Lemma 2.4 from the HB22 Draft statements (through
  `wholePlaneHalfBallFamilyStep_of_hb`) and the remaining steps: a sample of `h^ℂ` with its LQG measure
  (`WholePlaneLogLQGExistenceStep`), eq:gff (`ConeRestrictionStep`), locality of harmonic balls
  (`ConeHarmonicBallLocalityStep`) and strict growth (`ConeHarmonicBallStrictGrowthStep`).
* `coneHarmonicBalls_of_hb`: Theorem 2.3 from these, the quantum cone scaling input, Fact 2.2, positivity of the cone
  scale radius and the functional step of the half-disk family.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls

namespace MatedCRT

/-- **Lemma 2.4** from HB22 (Theorems 1.1, 5.5, Propositions 5.2, 5.3, 5.6, Lemmas 3.1-3.5, 5.8) and the transfer
steps. -/
theorem coneHarmonicBallsUpToFixedTime_of_hb (h11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (h55 : ExistenceHarmonicBallsStmt.{0}) (h56 : UniquenessHarmonicBallsStmt.{0})
    (h31 : LeastSupersolutionMemStmt.{0}) (h32 : ClusterOpenLaplacianStmt.{0}) (h33 : ClusterMonotoneStmt.{0})
    (h34 : ClusterConservationOfMassStmt.{0}) (h35 : ClusterCompatibilityStmt.{0})
    (h52 : ClusterContinuityStmt.{0}) (h53 : ClusterBoundaryMeasureZeroStmt.{0})
    (h58 : ClusterStrongCompatibilityStmt.{0}) (h0 : WholePlaneLogLQGExistenceStep) (h3 : ConeRestrictionStep)
    (h4 : ConeHarmonicBallLocalityStep) (h5 : ConeHarmonicBallStrictGrowthStep) :
    ConeHarmonicBallsUpToFixedTimeStmt :=
  coneHarmonicBallsUpToFixedTime_of_wholePlane h0
    (wholePlaneHalfBallFamilyStep_of_hb h11 h55 h56 h31 h32 h33 h34 h35 h52 h53 h58) h3 h4 h5

/-- **Theorem 2.3** from HB22, the transfer steps of Lemma 2.4, strict growth, the quantum cone scaling input
(DMS14 Proposition 4.13(i)), Fact 2.2, positivity of the cone scale radius and the functional step of the half-disk
family. -/
theorem coneHarmonicBalls_of_hb (h11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (h55 : ExistenceHarmonicBallsStmt.{0}) (h56 : UniquenessHarmonicBallsStmt.{0})
    (h31 : LeastSupersolutionMemStmt.{0}) (h32 : ClusterOpenLaplacianStmt.{0}) (h33 : ClusterMonotoneStmt.{0})
    (h34 : ClusterConservationOfMassStmt.{0}) (h35 : ClusterCompatibilityStmt.{0})
    (h52 : ClusterContinuityStmt.{0}) (h53 : ClusterBoundaryMeasureZeroStmt.{0})
    (h58 : ClusterStrongCompatibilityStmt.{0}) (h0 : WholePlaneLogLQGExistenceStep) (h3 : ConeRestrictionStep)
    (h4 : ConeHarmonicBallLocalityStep) (hgrow : ConeHarmonicBallStrictGrowthStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt) (hpos : ConeScaleRadiusPosStep)
    (hfun : ConeHalfBallFamilyFunctionalStep) : ConeHarmonicBallsStmt :=
  coneHarmonicBalls_of_steps
    (coneHarmonicBallsUpToFixedTime_of_hb h11 h55 h56 h31 h32 h33 h34 h35 h52 h53 h58 h0 h3 h4 hgrow)
    (coneScaleInvarianceUpToFixedTime_of_scaleRadiusPos hscale h22 hpos hgrow hfun)
    (coneFamilyAEMeasurableStep_of_inputs hscale hgrow h22 hpos hfun)

end MatedCRT
