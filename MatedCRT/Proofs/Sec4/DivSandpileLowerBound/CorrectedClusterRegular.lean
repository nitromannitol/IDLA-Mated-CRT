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


/-- Interior containment makes the stopped and global odometers agree on a
    regular mated map, without connectivity of the whole stopping domain. -/
theorem stoppedOdometer_eq_global_of_regular_interior
    {m : ℤ → ℤ → ℕ} {ε ρ t : ℝ} {η : ℝ → ℂ}
    (hd : IsRegularMatedMap m ε η) (ht : 0 < t)
    (h0 : (0 : ℤ) ∈ ballInterior ε η ρ)
    (hint : matedDiscreteCluster m ε η ρ t ⊆ vInterior m (ballInterior ε η ρ)) :
    stoppedOdometer m ε η ρ t = sandpileNormOdometer m (t / ε) := by
  classical
  let V := vComponent m (ballInterior ε η ρ) 0
  let φ := matedObstacle m ε η ρ t
  let w := discreteLeastSupersolution m V (vClosure m V) (fun a => (mdeg m a : ℝ)⁻¹) φ
  let A := discreteCluster (vClosure m V) w φ
  have hS : IsObstacleSetting m V 0 (fun a => (mdeg m a : ℝ)⁻¹) φ
      ((mdeg m 0 : ℝ)⁻¹ * (t / ε)) := by
    simpa [V, φ, matedDeg, mul_comm] using hd.isObstacleSetting ht h0
  have hA : matedDiscreteCluster m ε η ρ t = A := by
    simpa [A, V, w, φ, matedDeg] using hd.cluster_eq ht h0
  have hinterior : A ⊆ vInterior m V := by
    intro a ha
    have haV : a ∈ V := hS.cluster_subset ha
    have haI := hint (hA.symm ▸ ha)
    exact ⟨haV, fun b hab => mem_vComponent_of_adj haV (vComponent_subset h0 haV) (haI.2 b hab) hab⟩
  have hv := Sandpile.obstacle_odometer_eq_of_interior hS hinterior
  have hW : vClosure m V ⊆ cellVertices ε η (closedBall 0 ρ) :=
    (vClosure_vComponent_subset h0).trans (vClosure_ballInterior_subset hd.continuous hd.cells_meet)
  funext a
  have heq := congrFun hv a
  by_cases ha : a ∈ vClosure m V
  · have haW := hW ha
    have hw := hd.w_eq_gluedW ht h0 haW
    rw [gluedW_of_mem ha] at hw
    simpa [stoppedOdometer, haW, ha, V, w, φ, matedDeg, hw] using heq
  · by_cases haW : a ∈ cellVertices ε η (closedBall 0 ρ)
    · have hw := hd.w_eq_gluedW ht h0 haW
      rw [gluedW_of_not_mem ha] at hw
      have hφ := hd.obstacle_eq_zero_off ht h0 ha
      simpa [stoppedOdometer, haW, ha, hw, hφ] using heq
    · simpa [stoppedOdometer, haW, ha] using heq

end MatedCRT

#print axioms MatedCRT.stoppedOdometer_eq_global_of_regular_interior
#print axioms MatedCRT.sandpileCluster_eq_matedDiscreteCluster_closure_of_regular
