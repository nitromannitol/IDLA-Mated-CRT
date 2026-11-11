import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.LogBudgetBootstrap
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.RepeatedHalving
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.LogRatio

/-! Polynomial-scale stopping for logarithmic shell contraction. -/

namespace MatedCRT.Sec7

/-- Polynomial bounds on the initial maximum, threshold, and tested-radius
floor yield a shell threshold before a cubic-log horizon, provided the total
spatial budget is available up to that horizon. -/
theorem exists_shell_threshold_of_polynomial_log_bootstrap
    (O r u : ℕ → ℝ) (ε s a K α R D B δ p b ω H : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hs : 0 < s) (ha : 0 < a)
    (hω : 0 < ω) (haε : a ≤ ε ^ ω)
    (hsbound : s ≤ (1 + |Real.log a|) ^ 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hr0 : 0 ≤ r 0) (hO : ∀ k, 0 ≤ O k) (hO0 : 0 < O 0) (hB : 0 < B)
    (hOupper : O 0 ≤ ε ^ (-p)) (hBlower : ε ^ b ≤ B) (hpb : 0 ≤ p + b)
    (hH : ((p + b) / (ω * Real.log 2) + 2) * (2 / s + 2) *
      (1 + |Real.log a|) ^ 3 ≤ H)
    (hu : ∀ k, a ≤ u k ∧ u k ≤ 1)
    (hr : ∀ k, r (k + 1) ≤ max ((O k * K) ^ α) R)
    (hstep : ∀ k, B < O k →
      (∑ j ∈ Finset.range k, r j) + ((k : ℝ) + 1) * (2 * D) ≤ δ →
      (∀ j < k, O (j + 1) ≤ O j) →
      O (k + 1) ≤ (1 - s / (1 + |Real.log (u k)|) ^ 2) * O k)
    (hbudget : r 0 + (O 0 * K) ^ α /
      (1 - (1 - s / (1 + |Real.log a|) ^ 2) ^ α) +
      H * R + (H + 1) * (2 * D) ≤ δ) :
    ∃ τ : ℕ, (τ : ℝ) ≤ H ∧ O τ ≤ B ∧ (∀ k < τ, B < O k) ∧
      (∑ j ∈ Finset.range τ, r j) + ((τ : ℝ) + 1) * (2 * D) ≤ δ := by
  obtain ⟨M, N, hhalf, hN, hMN⟩ :=
    exists_polynomial_scale_halving_horizon ε a (O 0) B p b ω s hε hε1
      ha hω haε hO0 hB hOupper hBlower hpb hs
  have hMN' : ((M * N : ℕ) : ℝ) ≤ H := hMN.trans hH
  have hend := geometric_majorant_le_of_log_halving_blocks (O 0) s a B M N
    hO0.le hs hsbound hB hN hhalf
  have hbudget' : r 0 + (O 0 * K) ^ α /
      (1 - (1 - s / (1 + |Real.log a|) ^ 2) ^ α) +
      ((M * N : ℕ) : ℝ) * R + (((M * N : ℕ) : ℝ) + 1) * (2 * D) ≤ δ := by
    have h₁ := mul_le_mul_of_nonneg_right hMN' hR
    have h₂ := mul_le_mul_of_nonneg_right (add_le_add_right hMN' 1)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hD)
    linarith
  obtain ⟨τ, hτ, hτB, hτprev, hτbudget⟩ :=
    exists_shell_threshold_of_log_budget_bootstrap O r u s a K α R D B δ (M * N)
      hs ha hsbound hK hα hR hD hr0 (fun k _ => hO k) (fun k _ => hu k)
      hend (fun k _ => hr k) (fun k _ => hstep k) hbudget'
  exact ⟨τ, (Nat.cast_le.mpr hτ).trans hMN', hτB, hτprev, hτbudget⟩

end MatedCRT.Sec7
