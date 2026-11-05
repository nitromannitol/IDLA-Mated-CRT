import MatedCRT.Proofs.Sec5.MeanValueInequality.BoundaryContact
import MatedCRT.Proofs.Sec5.MeanValueInequality.ObstacleComparison
import MatedCRT.Proofs.Sec7.OdometerBoundMass.StoppedOdometer
import MatedCRT.Steps.Sec5.MeanValueInequality

/-!
# Contact outside the cluster without a connectivity hypothesis

The admissible zero function and the pointwise obstacle constraint give the
boundary contact needed for the mean-value comparison on an arbitrary graph.
-/

namespace MatedCRT

open Set Metric

/-- Finite-graph hypotheses for the obstacle comparison, together with the
two quantitative bounds on a prescribed set of interior vertices. -/
def MeanValueSurplusData (m : ℤ → ℤ → ℕ) (A B I : Set ℤ) (w : ℤ → ℝ)
    (K ε c C : ℝ) : Prop :=
  FiniteReversibleGreenData m A ∧
  (∀ a, m a (a + 1) ≠ 0) ∧ B.Finite ∧ A ⊆ B ∧ (0 : ℤ) ∈ A ∧
  (∀ b, ∀ a ∈ B, mLaplacian m (fun x => greenFn m B x b) a = -(if a = b then 1 else 0)) ∧
  (∀ a ∈ A, mLaplacian m w a = (mdeg m a : ℝ)⁻¹) ∧
  (∀ a ∈ I, c / ε ≤ w a + K * greenKernel m B 0 a ∧ normExitTime m A a ≤ C / ε)

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

/-- The deterministic mean-value comparison uses the surplus estimates and
finite-graph data, but does not require an obstacle-setting connectivity field. -/
theorem normalized_meanValue_of_surplus_direct {m : ℤ → ℤ → ℕ}
    {ε ρ t δ c C : ℝ} {η : ℝ → ℂ} (hε : 0 < ε) (ht : 0 < t)
    (hc : 0 < c) (hC : 0 < C)
    (hdata : MeanValueSurplusData m (matedDiscreteCluster m ε η ρ t)
      (ballInterior ε η ρ)
      {a ∈ matedDiscreteCluster m ε η ρ t |
        δ < infDist (vertexPoint ε η a)
          (frontier (fillCells ε η (matedDiscreteCluster m ε η ρ t)))}
      (matedLeastSupersolution m ε η ρ t) (t / ε) ε c C)
    {a : ℤ} (ha : a ∈ matedDiscreteCluster m ε η ρ t)
    (hdist : δ < infDist (vertexPoint ε η a)
      (frontier (fillCells ε η (matedDiscreteCluster m ε η ρ t)))) :
    (1 + c / C) * normExitTime m (matedDiscreteCluster m ε η ρ t) a ≤
      (t / ε) * greenKernel m (matedDiscreteCluster m ε η ρ t) a 0 := by
  obtain ⟨⟨hsymm, hlf, hA, hdeg, hfirstA⟩, hcons, hB, hAB, h0, hfirstB, hw, hbounds⟩ := hdata
  obtain ⟨hv, hq⟩ := hbounds a ⟨ha, hdist⟩
  have hboundary : ∀ x ∉ matedDiscreteCluster m ε η ρ t,
      matedLeastSupersolution m ε η ρ t x +
        (t / ε) * greenKernel m (ballInterior ε η ρ) 0 x ≤ 0 :=
    fun _ hx => (mated_surplus_zero_off_cluster_direct hε ht hx).le
  have hcomp := obstacle_surplus_le_green_sub_exit hsymm hlf hcons hA hB hAB h0 hfirstA hfirstB
    (matedLeastSupersolution m ε η ρ t) (t / ε) hw hboundary a
  rw [greenKernel_symm_of_firstStep hsymm hlf hA hdeg hfirstA 0 a] at hcomp
  exact normalized_meanValue_of_surplus_bounds hε hc hC hcomp hv hq

end MatedCRT
