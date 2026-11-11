import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.LogBudgetBootstrap
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.RepeatedHalving
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.LogHorizon

/-! Combining a logarithmic contraction, halving horizon, and spatial budget. -/

namespace MatedCRT.Sec7

/-- A logarithmic initial-to-target ratio and a sufficiently long halving
block close the radius-budget bootstrap and yield a first threshold crossing. -/
theorem exists_shell_threshold_of_log_halving_bootstrap
    (O r u : ℕ → ℝ) (s a K α R D B δ C : ℝ) (M N : ℕ)
    (hs : 0 < s) (ha : 0 < a)
    (hsbound : s ≤ (1 + |Real.log a|) ^ 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hB : 0 < B) (hr0 : 0 ≤ r 0) (hO : ∀ k ≤ M * N, 0 ≤ O k)
    (hO0 : 0 < O 0)
    (hratio : Real.log (O 0 / B) ≤ C * (1 + |Real.log a|) * Real.log 2)
    (hM : C * (1 + |Real.log a|) ≤ (M : ℝ))
    (hN : 2 * (1 + |Real.log a|) ^ 2 < (N : ℝ) * s)
    (hu : ∀ k < M * N, a ≤ u k ∧ u k ≤ 1)
    (hr : ∀ k < M * N, r (k + 1) ≤ max ((O k * K) ^ α) R)
    (hstep : ∀ k < M * N, B < O k →
      (∑ j ∈ Finset.range k, r j) + ((k : ℝ) + 1) * (2 * D) ≤ δ →
      (∀ j < k, O (j + 1) ≤ O j) →
      O (k + 1) ≤ (1 - s / (1 + |Real.log (u k)|) ^ 2) * O k)
    (hbudget : r 0 + (O 0 * K) ^ α /
      (1 - (1 - s / (1 + |Real.log a|) ^ 2) ^ α) +
      ((M * N : ℕ) : ℝ) * R + (((M * N : ℕ) : ℝ) + 1) * (2 * D) ≤ δ) :
    ∃ τ : ℕ, τ ≤ M * N ∧ O τ ≤ B ∧ (∀ k < τ, B < O k) ∧
      (∑ j ∈ Finset.range τ, r j) + ((τ : ℝ) + 1) * (2 * D) ≤ δ := by
  have hhalf : O 0 * (1 / 2 : ℝ) ^ M ≤ B :=
    halving_blocks_reach_threshold (O 0) B (1 + |Real.log a|) C M hO0 hB hratio hM
  have hend := geometric_majorant_le_of_log_halving_blocks (O 0) s a B M N
    hO0.le hs hsbound hB hN hhalf
  exact exists_shell_threshold_of_log_budget_bootstrap O r u s a K α R D B δ (M * N)
    hs ha hsbound hK hα hR hD hr0 hO hu hend hr hstep hbudget

end MatedCRT.Sec7
