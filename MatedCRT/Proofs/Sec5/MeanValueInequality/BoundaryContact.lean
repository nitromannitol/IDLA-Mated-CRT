import MatedCRT.Proofs.Sec4.Equibounded
import MatedCRT.Steps.Sec4.ObstacleSpecialization

/-!
# Obstacle contact outside the discrete cluster

At a vertex outside the cluster, the obstacle surplus vanishes.  This gives
the boundary condition used in the proof of Lemma 5.3.  In particular it is
the sum of the least supersolution and the ambient Green potential that
vanishes; the two summands need not vanish individually.
-/

namespace MatedCRT

open Set Metric

/-- Outside the cluster the least supersolution equals its obstacle, including
vertices outside the domain on which the obstacle problem is constrained. -/
theorem mated_surplus_eq_zero_off_cluster {m : ℤ → ℤ → ℕ} {ε ρ t : ℝ} {η : ℝ → ℂ}
    (hS : IsMatedObstacleSetting m ε η ρ t)
    (hW : vClosure m (ballInterior ε η ρ) ⊆ cellVertices ε η (closedBall 0 ρ))
    {a : ℤ} (ha : a ∉ matedDiscreteCluster m ε η ρ t) :
    matedLeastSupersolution m ε η ρ t a = matedObstacle m ε η ρ t a := by
  by_cases haV : a ∈ ballInterior ε η ρ
  · have haU : a ∈ cellVertices ε η (ball 0 ρ) := ballInterior_subset_cellVertices_ball haV
    have hle : matedObstacle m ε η ρ t a ≤ matedLeastSupersolution m ε η ρ t a := by
      rw [matedLeastSupersolution_eq, dls_eq_of_mem_vClosure hS hW matedObstacle_eq_zero_off_vClosure (Or.inl haV)]
      exact hS.obstacle_le_w a (Or.inl haV)
    have hnlt : ¬ matedObstacle m ε η ρ t a < matedLeastSupersolution m ε η ρ t a := by
      intro hlt
      exact ha ⟨haU, hlt⟩
    exact le_antisymm (not_lt.1 hnlt) hle
  · have hφ : matedObstacle m ε η ρ t a = 0 := matedObstacle_eq_zero_of_not_mem haV
    rw [hφ]
    by_cases haW : a ∈ cellVertices ε η (closedBall 0 ρ)
    · rw [matedLeastSupersolution_eq]
      by_cases haCl : a ∈ vClosure m (ballInterior ε η ρ)
      · have hab : a ∈ vBoundary m (ballInterior ε η ρ) := haCl.resolve_left haV
        rw [dls_eq_of_mem_vClosure hS hW matedObstacle_eq_zero_off_vClosure haCl]
        exact (hS.w_boundary a hab).1
      · exact dls_eq_zero_of_not_mem_vClosure hS matedObstacle_eq_zero_off_vClosure haW haCl
    · unfold matedLeastSupersolution
      exact Equibounded.discreteLeastSupersolution_eq_zero_of_not_mem haV haW

/-- The boundary condition in the obstacle comparison. -/
theorem mated_surplus_zero_off_cluster {m : ℤ → ℤ → ℕ} {ε ρ t : ℝ} {η : ℝ → ℂ}
    (hS : IsMatedObstacleSetting m ε η ρ t)
    (hW : vClosure m (ballInterior ε η ρ) ⊆ cellVertices ε η (closedBall 0 ρ))
    {a : ℤ} (ha : a ∉ matedDiscreteCluster m ε η ρ t) :
    matedLeastSupersolution m ε η ρ t a +
      t / ε * greenKernel m (ballInterior ε η ρ) 0 a = 0 := by
  rw [mated_surplus_eq_zero_off_cluster hS hW ha]
  simp [matedObstacle]

end MatedCRT
