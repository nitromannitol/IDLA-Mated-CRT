import MatedCRT.Proofs.Sandpile.Properties

/-! The stopped odometer equation under the global comparison. -/

namespace MatedCRT.Sandpile

open Set Metric Classical

/-- Equation `laplacian-of-uteps` on the obstacle cluster, obtained from
the global least action principle when the stopped and global odometers agree. -/
theorem stopped_equation_of_comparison {m : ℤ → ℤ → ℕ} {ε ρ t : ℝ} {η : ℝ → ℂ}
    (hlf : IsLocallyFiniteMult m) (hloop : ∀ a, m a a = 0)
    (hdeg : ∀ a, 0 < mdeg m a) (hne : (admissible m (t / ε)).Nonempty)
    (hM : 0 ≤ t / ε)
    (heq : stoppedOdometer m ε η ρ t = sandpileNormOdometer m (t / ε))
    {a : ℤ} (ha : a ∈ cellVertices ε η (ball 0 ρ)) :
    0 ≤ mLaplacian m (stoppedOdometer m ε η ρ t) a +
      (mdeg m 0 : ℝ)⁻¹ * (t / ε) * diracZero a ∧
    mLaplacian m (stoppedOdometer m ε η ρ t) a +
      (mdeg m 0 : ℝ)⁻¹ * (t / ε) * diracZero a ≤ (mdeg m a : ℝ)⁻¹ ∧
    0 ≤ stoppedOdometer m ε η ρ t a ∧
    (a ∈ matedDiscreteCluster m ε η ρ t →
      mLaplacian m (stoppedOdometer m ε η ρ t) a +
        (mdeg m 0 : ℝ)⁻¹ * (t / ε) * diracZero a = (mdeg m a : ℝ)⁻¹) ∧
    (a ∉ matedDiscreteCluster m ε η ρ t → stoppedOdometer m ε η ρ t a = 0) := by
  have haW : a ∈ cellVertices ε η (closedBall 0 ρ) := by
    rcases ha with ⟨z, hz, hzB⟩
    exact ⟨z, hz, ball_subset_closedBall hzB⟩
  have hiff : a ∈ matedDiscreteCluster m ε η ρ t ↔ 0 < stoppedOdometer m ε η ρ t a := by
    simp [matedDiscreteCluster, discreteCluster, stoppedOdometer, ha, haW, sub_pos]
  have hnonneg : 0 ≤ stoppedOdometer m ε η ρ t a := by
    rw [heq]
    exact normOdometer_nonneg hne a
  refine ⟨?_, ?_, hnonneg, ?_, ?_⟩
  · rw [heq]
    exact normalized_final_nonneg hlf hloop hdeg hne hM a
  · rw [heq]
    exact (normOdometer_mem_admissible hlf hne).2 a
  · intro haΛ
    have hu := hiff.mp haΛ
    rw [heq] at hu ⊢
    exact normalized_laplacian_eq_of_odometer_pos hlf hloop hdeg hne hu
  · intro haΛ
    exact le_antisymm (not_lt.mp (fun h => haΛ (hiff.mpr h))) hnonneg

end MatedCRT.Sandpile
