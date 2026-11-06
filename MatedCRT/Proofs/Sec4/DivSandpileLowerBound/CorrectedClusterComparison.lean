import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.ClusterComparison
import MatedCRT.Proofs.Sandpile.ClusterIdentityCorrected

/-! The one-sided cluster comparison at the corrected scale `ε < t`.
The reverse inclusion requires stopped/global consistency. -/

namespace MatedCRT

open Set

/-- The odometer comparison places the obstacle cluster inside the support of
    the global odometer. -/
theorem matedDiscreteCluster_subset_globalOdometerSupport
    {m : ℤ → ℤ → ℕ} {ε ρ t : ℝ} {η : ℝ → ℂ}
    (hlower : ∀ a ∈ cellVertices ε η (Metric.ball 0 ρ),
      matedLeastSupersolution m ε η ρ t a - matedObstacle m ε η ρ t a ≤
        sandpileNormOdometer m (t / ε) a) :
    matedDiscreteCluster m ε η ρ t ⊆ Function.support (sandpileNormOdometer m (t / ε)) := by
  intro a ha
  have ha' : a ∈ cellVertices ε η (Metric.ball 0 ρ) ∧
      matedObstacle m ε η ρ t a < matedLeastSupersolution m ε η ρ t a := ha
  have hp : 0 < sandpileNormOdometer m (t / ε) a := by linarith [hlower a ha'.1, ha'.2]
  exact ne_of_gt hp

/-- Corrected equation `eq:cluster-and-lambdat`, one-sided without the
    additional stopped/global consistency hypothesis (paper lines 1870–1874). -/
theorem matedDiscreteCluster_closure_subset_sandpileCluster
    {m : ℤ → ℤ → ℕ} {ε ρ t : ℝ} {η : ℝ → ℂ}
    (hlf : IsLocallyFiniteMult m) (hsymm : ∀ a b, m a b = m b a)
    (hloop : ∀ a, m a a = 0) (hdeg : ∀ a, 0 < mdeg m a)
    (hne : (Sandpile.admissible m (t / ε)).Nonempty) (hε : 0 < ε) (hεt : ε < t)
    (hlower : ∀ a ∈ cellVertices ε η (Metric.ball 0 ρ),
      matedLeastSupersolution m ε η ρ t a - matedObstacle m ε η ρ t a ≤
        sandpileNormOdometer m (t / ε) a) :
    vClosure m (matedDiscreteCluster m ε η ρ t) ⊆ sandpileCluster m (t / ε) := by
  rw [Sandpile.cluster_eq_closure_of_mesh_lt_time hlf hsymm hloop hdeg hne hε hεt]
  have hsub := matedDiscreteCluster_subset_globalOdometerSupport hlower
  intro b hb
  rcases hb with hb | ⟨_, a, ha, hab⟩
  · exact Or.inl (hsub hb)
  · by_cases hb' : b ∈ Function.support (sandpileNormOdometer m (t / ε))
    · exact Or.inl hb'
    · exact Or.inr ⟨hb', a, hsub ha, hab⟩

/-- The stopped-cluster equality in the corrected paper, under the stated
    consistency of stopped and global positive odometer sets. -/
theorem sandpileCluster_eq_matedDiscreteCluster_closure_of_consistency
    {m : ℤ → ℤ → ℕ} {ε ρ t : ℝ} {η : ℝ → ℂ}
    (hlf : IsLocallyFiniteMult m) (hsymm : ∀ a b, m a b = m b a)
    (hloop : ∀ a, m a a = 0) (hdeg : ∀ a, 0 < mdeg m a)
    (hne : (Sandpile.admissible m (t / ε)).Nonempty) (hε : 0 < ε) (hεt : ε < t)
    (hconsistency : Function.support (sandpileNormOdometer m (t / ε)) =
      matedDiscreteCluster m ε η ρ t) :
    sandpileCluster m (t / ε) = vClosure m (matedDiscreteCluster m ε η ρ t) := by
  rw [Sandpile.cluster_eq_closure_of_mesh_lt_time hlf hsymm hloop hdeg hne hε hεt,
    hconsistency]

end MatedCRT
