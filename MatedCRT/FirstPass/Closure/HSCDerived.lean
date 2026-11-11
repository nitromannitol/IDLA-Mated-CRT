import MatedCRT.FirstPass.Frozen.S5Cited
import HarmonicBalls.Proofs.Sec5.StrongCompatibilityAssembly

/-! # Frozen cluster strong compatibility derived from the all-scales volume growth input

The statement `FrozenClusterStrongCompatibility` (Lemma 5.8, for every bounded open set `U`) is derived from the
all-scales volume growth input `FrozenLQGVolumeGrowthAllScales` (the input `hI2`) in the Harmonic-Balls Lean
development. The proof route differs from the printed proof of Lemma 5.8 (which uses continuity of the Green function
up to the boundary of `U`): it proves the all-`U` statement by exhaustion of `U` by Green-regular domains. The
hypothesis `hI2` is unchanged.
-/

namespace MatedCRT

/-- `FrozenClusterStrongCompatibility` (Lemma 5.8, all bounded open `U`) from `FrozenLQGVolumeGrowthAllScales` (`hI2`),
by the Harmonic-Balls theorem `HarmonicBalls.clusterStrongCompatibilityStmt_of_volumeGrowth`
(HarmonicBalls/Proofs/Sec5/StrongCompatibilityAssembly.lean:15). The two Props are `LQGVolumeGrowthAllScalesStmt.{0}`
and `ClusterStrongCompatibilityStmt.{0}` (Harmonic-Balls Draft/Section2.lean:122, Draft/Section5.lean:246). -/
theorem frozenClusterStrongCompatibility_of_volumeGrowth (hI2 : FrozenLQGVolumeGrowthAllScales) :
    FrozenClusterStrongCompatibility :=
  HarmonicBalls.clusterStrongCompatibilityStmt_of_volumeGrowth hI2

#print axioms frozenClusterStrongCompatibility_of_volumeGrowth

end MatedCRT
