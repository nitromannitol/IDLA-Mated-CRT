import MatedCRT.Steps.SecA.DiscreteObstacle
import MatedCRT.Proofs.SecA.DiscreteObstacle
import MatedCRT.Proofs.SecA.DiscreteDivergence

/-!
# Appendix A: proofs of the steps and of Lemmas A.1-A.4

The steps of MatedCRT/Steps/SecA/DiscreteObstacle.lean from the lemmas of MatedCRT/Proofs/SecA/DiscreteObstacle.lean,
and the four statements of MatedCRT/Draft/SectionA.lean. No literature input is used.
-/

namespace MatedCRT

open Set Finset Classical

theorem obstacleBoundsStep : ObstacleBoundsStep :=
  fun _ _ _ _ _ _ _ hS a ha => ⟨hS.obstacle_le_w a ha, hS.w_nonpos a ha⟩

theorem obstacleComparisonStep : ObstacleComparisonStep :=
  fun _ _ _ _ _ _ _ hS 𝔮 hq hqb a ha => hS.q_le 𝔮 hq hqb _ hS.w_mem_admissible a ha

theorem obstacleSupersolutionStep : ObstacleSupersolutionStep :=
  fun _ _ _ _ _ _ _ hS a ha => hS.lap_w_le a ha

theorem obstacleClusterLaplacianStep : ObstacleClusterLaplacianStep :=
  fun _ _ _ _ _ _ _ hS a ha => hS.lap_w_eq_on_cluster a ha

theorem obstacleLaplacianNonnegStep : ObstacleLaplacianNonnegStep :=
  fun _ _ _ _ _ _ _ hS a ha => hS.lap_w_nonneg a ha

theorem obstacleClusterPreconnectedStep : ObstacleClusterPreconnectedStep :=
  fun _ _ _ _ _ _ _ hS => hS.cluster_preconnected

theorem obstacleOriginStep : ObstacleOriginStep :=
  fun _ _ _ _ _ _ _ hS ht => hS.origin_mem_cluster ht

theorem obstacleClusterCardStep : ObstacleClusterCardStep := by
  intro α m V o 𝔯 φ 𝔱 hS hr
  have hΛ := hS.cluster_finite
  have hsub : hΛ.toFinset ⊆ hS.finite.toFinset := Set.Finite.toFinset_subset_toFinset.2 hS.cluster_subset
  have hone : ∀ a ∈ hΛ.toFinset, lapSum hS.hlf (obstacleW m V 𝔯 φ) a = 1 := by
    intro a ha
    have haΛ := hΛ.mem_toFinset.1 ha
    have haV := hS.cluster_subset haΛ
    have hD : (mdeg m a : ℝ) ≠ 0 := by exact_mod_cast (hS.mdeg_pos a haV).ne'
    rw [← mLaplacian_mul_mdeg hS.hlf, hS.lap_w_eq_on_cluster a haΛ, hr a haV, inv_mul_cancel₀ hD]
  have hnonneg : ∀ a ∈ hS.finite.toFinset, a ∉ hΛ.toFinset → 0 ≤ lapSum hS.hlf (obstacleW m V 𝔯 φ) a := by
    intro a ha _
    rw [← mLaplacian_mul_mdeg hS.hlf]
    exact mul_nonneg (hS.lap_w_nonneg a (hS.finite.mem_toFinset.1 ha)) (Nat.cast_nonneg _)
  rw [Set.ncard_eq_toFinset_card _ hΛ, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
    ← Finset.sum_congr rfl hone]
  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg) hS.sum_lapSum_w_le

theorem obstacleMassIdentityStep : ObstacleMassIdentityStep := by
  intro α m V o 𝔯 φ 𝔱 hS _ hint
  rw [finsum_mem_eq_finite_toFinset_sum _ hS.finite]
  rw [Finset.sum_congr rfl fun a _ => mLaplacian_mul_mdeg hS.hlf (obstacleW m V 𝔯 φ) a]
  exact hS.sum_lapSum_w_eq_of_subset hint

/-- **Lemma A.2** (lemma:discrete-basic-properties-general, line 3413). -/
theorem discreteBasicPropertiesGeneral : DiscreteBasicPropertiesGeneralStmt :=
  discreteBasicPropertiesGeneral_of_steps obstacleBoundsStep obstacleComparisonStep obstacleSupersolutionStep

/-- **Lemma A.3** (lemma:discrete-laplacian-bound-general, line 3448). -/
theorem discreteLaplacianBoundGeneral : DiscreteLaplacianBoundGeneralStmt :=
  discreteLaplacianBoundGeneral_of_steps obstacleSupersolutionStep obstacleClusterLaplacianStep
    obstacleLaplacianNonnegStep obstacleClusterPreconnectedStep obstacleOriginStep

/-- **Lemma A.4** (lemma:discrete-conservation-of-mass-general, line 3528). -/
theorem discreteConservationOfMassGeneral : DiscreteConservationOfMassGeneralStmt :=
  discreteConservationOfMassGeneral_of_steps obstacleClusterCardStep obstacleMassIdentityStep

end MatedCRT
