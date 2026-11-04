import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicFiniteBudget

/-! Passing the delayed radius budget to every spatial shell prefix. -/

namespace MatedCRT.Sec7

/-- A bound for delayed radii through a stopping time controls the spatial
budget at every earlier shell, including the initial radius and diameters. -/
theorem shell_prefix_budget_of_delayed_sum
    (r : ℕ → ℝ) (τ : ℕ) (D T H : ℝ)
    (hD : 0 ≤ D) (hr : ∀ k ≤ τ, 0 ≤ r k) (hτ : (τ : ℝ) ≤ H)
    (hsum : (∑ k ∈ Finset.range τ, r (k + 1)) ≤ T) :
    ∀ k ≤ τ, (∑ j ∈ Finset.range k, r j) + ((k : ℝ) + 1) * (2 * D) ≤
      r 0 + T + (H + 1) * (2 * D) := by
  have hdelayed : ∀ k < τ, 0 ≤ r (k + 1) := fun k hk => hr (k + 1) (by omega)
  intro k hk
  have hkH : (k : ℝ) ≤ H := (Nat.cast_le.mpr hk).trans hτ
  have hdiam := mul_le_mul_of_nonneg_right (add_le_add_right hkH 1)
    (by linarith : 0 ≤ 2 * D)
  cases k with
  | zero =>
    have hT : 0 ≤ T := (Finset.sum_nonneg (fun i hi => hdelayed i (Finset.mem_range.mp hi))).trans hsum
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_add]
    nlinarith [hr 0 (Nat.zero_le τ)]
  | succ k =>
    have hsub : (∑ i ∈ Finset.range k, r (i + 1)) ≤
        ∑ i ∈ Finset.range τ, r (i + 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      intro i hi _
      exact hdelayed i (Finset.mem_range.mp hi)
    rw [Finset.sum_range_succ']
    nlinarith

end MatedCRT.Sec7
