import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.CorrectedClusterComparison
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.OdometerComparison
import MatedCRT.Proofs.Sandpile.ComponentComparison

/-! Corrected stopped-cluster identity without connectivity of the stopping domain. -/

namespace MatedCRT

open Set Metric

/-- The stopped-cluster identity at `ε < t`, assuming its cluster stays in
    the graph interior. The stopping domain need not be connected. -/
theorem sandpileCluster_eq_matedDiscreteCluster_closure_of_regular
    {m : ℤ → ℤ → ℕ} {ε ρ t : ℝ} {η : ℝ → ℂ}
    (hd : IsRegularMatedMap m ε η) (hεt : ε < t)
    (h0 : (0 : ℤ) ∈ ballInterior ε η ρ)
    (hint : matedDiscreteCluster m ε η ρ t ⊆ vInterior m (ballInterior ε η ρ)) :
    sandpileCluster m (t / ε) = vClosure m (matedDiscreteCluster m ε η ρ t) := by
  have ht : 0 < t := hd.pos.trans hεt
  have hdeg : ∀ a, 0 < mdeg m a := fun a => mdeg_pos_of_ne_zero hd.locallyFinite (hd.succ a)
  have hconn := Sandpile.connected_of_consecutive_edges hd.symm hd.succ
  obtain ⟨v, hv, _⟩ := Sandpile.exists_finite_stabilizer hd.locallyFinite hd.symm hd.loopless hdeg hconn (t / ε)
  have hne : (Sandpile.admissible m (t / ε)).Nonempty := ⟨v, hv⟩
  have hlower : ∀ a ∈ cellVertices ε η (ball 0 ρ),
      matedLeastSupersolution m ε η ρ t a - matedObstacle m ε η ρ t a ≤
        sandpileNormOdometer m (t / ε) a := by
    intro a ha
    apply Sandpile.matedObstacle_gap_le_normOdometer hd.locallyFinite hd.symm hd.succ
      hd.finite_ballInterior hne
    obtain ⟨z, hz, hzball⟩ := ha
    exact ⟨z, hz, ball_subset_closedBall hzball⟩
  have h0cluster : (0 : ℤ) ∈ matedDiscreteCluster m ε η ρ t :=
    (matedLaplacianBound_of_regular hd ht).2.2.2 ((one_lt_div hd.pos).2 hεt) h0
  apply Set.Subset.antisymm
  · have h := Sandpile.global_cluster_subset_stopped_closure_of_regular hd ht h0 hint
    simpa only [Set.insert_eq_of_mem (show (0 : ℤ) ∈ vClosure m (matedDiscreteCluster m ε η ρ t)
      from Or.inl h0cluster)] using h
  · exact matedDiscreteCluster_closure_subset_sandpileCluster hd.locallyFinite hd.symm hd.loopless hdeg
      hne hd.pos hεt hlower

end MatedCRT

#print axioms MatedCRT.sandpileCluster_eq_matedDiscreteCluster_closure_of_regular
