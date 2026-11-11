import HarmonicBalls.Assembly.ExistenceUniqueness
import HarmonicBalls.Proofs.Sec3.OpenLaplacian
import HarmonicBalls.Proofs.Sec5.UniquenessFromVolumeGrowth
import HarmonicBalls.Proofs.Sec6.VolumeGrowthConsequences
import HarmonicBalls.Proofs.Sec8.ClusterBoundary
import HarmonicBalls.Proofs.Sec9.HarmonicBoundaryAssembly
import HarmonicBalls.Proofs.Sec9.VolumeGrowthAssembly
import HarmonicBalls.Steps.Sec5.ClusterBounds

/-!
# Uniqueness of harmonic balls and the boundary of the clusters, from volume growth

Three results of the harmonic-balls paper (Bou-Rabee and Gwynne, arXiv:2208.11795) which the counted theorems of this
repository bind as hypotheses follow, inside the Harmonic-Balls package, from hypotheses which the same theorems bind:

* Proposition 5.6 (uniqueness of harmonic balls, `UniquenessHarmonicBallsStmt`) from the volume-growth statement
  `LQGVolumeGrowthAllScalesStmt` alone: the boundary inclusion of Lemma 9.3
  (`HarmonicBalls.harmonicBallBoundarySubset_of_volumeGrowth`) and the regular-open comparison of Lemma 9.4
  (`HarmonicBalls.regularOpenEqOfAEEq_of_volumeGrowth`) both follow from volume growth;
* Theorem 1.1 (existence and uniqueness, `ExistenceUniquenessHarmonicBallsStmt`) from Proposition 5.5 (existence) and
  volume growth;
* Proposition 5.3 (the boundary of a cluster has LQG measure zero, `ClusterBoundaryMeasureZeroStmt`) from volume
  growth and Lemma 8.2 (`TypicalPointManyGoodScalesStmt`): Lemma 3.2 and Lemma 6.11 follow from volume growth, and
  Proposition 8.1 follows from Lemmas 3.2, 6.11 and 8.2.

Each theorem is a composition of theorems of the Harmonic-Balls package; no statement is changed.
-/

namespace MatedCRT

open HarmonicBalls

universe u

/-- **Proposition 5.6 of the harmonic-balls paper** (uniqueness of harmonic balls) from the volume-growth statement:
Lemmas 9.3 and 9.4 follow from volume growth. -/
theorem uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    UniquenessHarmonicBallsStmt.{u} :=
  uniquenessHarmonicBalls_of_boundary_and_volumeGrowth hI2 (harmonicBallBoundarySubset_of_volumeGrowth hI2)
    (regularOpenEqOfAEEq_of_volumeGrowth hI2)

/-- **Theorem 1.1 of the harmonic-balls paper** (existence and uniqueness of harmonic balls) from Proposition 5.5
(existence) and the volume-growth statement. -/
theorem existenceUniquenessHarmonicBallsStmt_of_existence_volumeGrowth (h55 : ExistenceHarmonicBallsStmt.{u})
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) : ExistenceUniquenessHarmonicBallsStmt.{u} :=
  existenceUniquenessHarmonicBallsStmt_of_sec5 h55 (uniquenessHarmonicBallsStmt_of_volumeGrowth hI2)

/-- **Proposition 5.3 of the harmonic-balls paper** (the boundary of a cluster has LQG measure zero) from the
volume-growth statement and Lemma 8.2 (a typical point has many good scales): Proposition 8.1 follows from
Lemmas 3.2, 6.11 and 8.2, and the first two follow from volume growth. -/
theorem clusterBoundaryMeasureZeroStmt_of_volumeGrowth_typicalPoint (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) : ClusterBoundaryMeasureZeroStmt.{u} :=
  clusterBoundaryMeasureZero_of_steps
    (boundaryMeasureZeroOfCompactClusterStmt_of_steps (clusterOpenLaplacian_proved hI2)
      (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) h82)

end MatedCRT
