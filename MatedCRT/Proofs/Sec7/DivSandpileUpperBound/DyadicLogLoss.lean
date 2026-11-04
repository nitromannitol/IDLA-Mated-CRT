import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.HalvingTime
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicBudget

/-! Radius-dependent logarithmic losses in successive halving blocks. -/

namespace MatedCRT.Sec7

/-- A geometric lower bound on a test radius gives a logarithmic loss which
grows at most linearly with the halving-block index. -/
theorem log_loss_le_of_geometric_radius_lower_bound
    {a q r : ℝ} (n : ℕ) (ha : 0 < a) (hq : 0 < q)
    (har : a * q ^ n ≤ r) (hr : r ≤ 1) :
    1 + |Real.log r| ≤ 1 + |Real.log a| + (n : ℝ) * |Real.log q| := by
  have hfloor : 0 < a * q ^ n := mul_pos ha (pow_pos hq n)
  have hbound := log_loss_le_of_radius_lower_bound hfloor har hr
  have hlog : |Real.log (a * q ^ n)| ≤ |Real.log a| + (n : ℝ) * |Real.log q| := by
    rw [Real.log_mul (ne_of_gt ha) (ne_of_gt (pow_pos hq n)), Real.log_pow]
    calc
      _ ≤ |Real.log a| + |(n : ℝ) * Real.log q| := abs_add_le _ _
      _ = _ := by simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)]
  linarith

/-- If all test radii in a block have a geometric lower bound, the block
halves within any horizon dominating its explicit quadratic log loss. -/
theorem exists_halving_before_of_geometric_radius_lower_bound
    (O r : ℕ → ℝ) (s a q : ℝ) (j N : ℕ)
    (hO : 0 < O 0) (hs : 0 < s) (ha : 0 < a) (hq : 0 < q)
    (hN : 2 * (1 + |Real.log a| + (j : ℝ) * |Real.log q|) ^ 2 < (N : ℝ) * s)
    (hr : ∀ k < N, a * q ^ j ≤ r k ∧ r k ≤ 1)
    (hstep : ∀ k < N, O 0 / 2 < O k →
      O (k + 1) ≤ (1 - s / (1 + |Real.log (r k)|) ^ 2) * O k) :
    ∃ k ≤ N, O k ≤ O 0 / 2 := by
  apply exists_halving_before_of_log_loss O r s
    (1 + |Real.log a| + (j : ℝ) * |Real.log q|) N hO hs (by positivity) hN
  · intro k hk
    exact log_loss_le_of_geometric_radius_lower_bound j ha hq (hr k hk).1 (hr k hk).2
  · exact hstep

end MatedCRT.Sec7
