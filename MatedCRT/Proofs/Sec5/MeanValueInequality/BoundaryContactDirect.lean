import MatedCRT.Proofs.Sec5.MeanValueInequality.BoundaryContact
import MatedCRT.Proofs.Sec7.OdometerBoundMass.StoppedOdometer

/-!
# Contact outside the cluster without a connectivity hypothesis

The admissible zero function and the pointwise obstacle constraint give the
boundary contact needed for the mean-value comparison on an arbitrary graph.
-/

namespace MatedCRT

open Set Metric

/-- At every vertex outside the discrete cluster the least supersolution
equals its obstacle. -/
theorem mated_surplus_eq_zero_off_cluster_direct {m : ℤ → ℤ → ℕ}
    {ε ρ t : ℝ} {η : ℝ → ℂ} (hε : 0 < ε) (ht : 0 < t)
    {a : ℤ} (ha : a ∉ matedDiscreteCluster m ε η ρ t) :
    matedLeastSupersolution m ε η ρ t a = matedObstacle m ε η ρ t a := by
  by_cases haU : a ∈ cellVertices ε η (ball 0 ρ)
  · have haW := Sec7.cellVertices_mono ball_subset_closedBall haU
    have hle := Sec7.matedObstacle_le_matedLeastSupersolution
      (m := m) (η := η) (ρ := ρ) hε ht haW
    have hnlt : ¬ matedObstacle m ε η ρ t a < matedLeastSupersolution m ε η ρ t a :=
      fun h => ha ⟨haU, h⟩
    exact le_antisymm (not_lt.1 hnlt) hle
  · have haV : a ∉ ballInterior ε η ρ := fun h => haU (ballInterior_subset_cellVertices_ball h)
    by_cases haW : a ∈ cellVertices ε η (closedBall 0 ρ)
    · exact le_antisymm
        (Sec7.matedLeastSupersolution_le_obstacle_of_not_mem_ballInterior
          (m := m) (η := η) (ρ := ρ) hε ht haW haV)
        (Sec7.matedObstacle_le_matedLeastSupersolution
          (m := m) (η := η) (ρ := ρ) hε ht haW)
    · rw [matedObstacle_eq_zero_of_not_mem haV]
      unfold matedLeastSupersolution
      exact Equibounded.discreteLeastSupersolution_eq_zero_of_not_mem haV haW

/-- The boundary condition used in the mean-value comparison holds without
any assumption that the interior vertex set is connected. -/
theorem mated_surplus_zero_off_cluster_direct {m : ℤ → ℤ → ℕ}
    {ε ρ t : ℝ} {η : ℝ → ℂ} (hε : 0 < ε) (ht : 0 < t)
    {a : ℤ} (ha : a ∉ matedDiscreteCluster m ε η ρ t) :
    matedLeastSupersolution m ε η ρ t a +
      t / ε * greenKernel m (ballInterior ε η ρ) 0 a = 0 := by
  rw [mated_surplus_eq_zero_off_cluster_direct hε ht ha]
  simp [matedObstacle]

end MatedCRT
