import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicLogLoss

/-! Qualitative vanishing of the dyadic shell-radius budget. -/

namespace MatedCRT.Sec7

open Filter Topology

/-- The initial-radius contribution to the dyadic budget vanishes without
requiring a polynomial rate in the mesh. -/
theorem tendsto_dyadic_initial_radius_budget
    {α C : ℝ} (hα : 0 < α) :
    Tendsto (fun x : ℝ => C * (x ^ α * (1 + |Real.log x|) ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
  simpa using (tendsto_rpow_mul_quadratic_log_loss hα).const_mul C

/-- Halving blocks with geometrically decaying radius and logarithmically
growing lengths have a radius budget controlled by the initial radius and the
accumulated floor contribution. -/
theorem halving_blocks_radius_budget_qualitative
    (length : ℕ → ℕ) (radius : ℕ → ℕ → ℝ) (N : ℕ)
    (q x α F C B : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (hx : 0 ≤ x)
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hlen : ∀ j < N, (length j : ℝ) ≤
      C * (1 + |Real.log x| + B * (j : ℝ)) ^ 2)
    (hrad : ∀ j < N, ∀ k < length j, radius j k ≤ x ^ α * q ^ j + F) :
    (∑ j ∈ Finset.range N, ∑ k ∈ Finset.range (length j), radius j k) ≤
      (C * (1 + B) ^ 2 * ∑' j : ℕ, ((j : ℝ) + 1) ^ 2 * q ^ j) *
        (x ^ α * (1 + |Real.log x|) ^ 2) +
        F * ∑ j ∈ Finset.range N, (length j : ℝ) := by
  let A := 1 + |Real.log x|
  let S := ∑' j : ℕ, ((j : ℝ) + 1) ^ 2 * q ^ j
  have hA : 1 ≤ A := by dsimp [A]; have := abs_nonneg (Real.log x); linarith
  have hS : 0 ≤ S := by
    dsimp [S]
    exact tsum_nonneg (fun j => mul_nonneg (sq_nonneg _) (pow_nonneg hq j))
  have hAB : (A + B) ^ 2 ≤ (1 + B) ^ 2 * A ^ 2 := by
    have hle : A + B ≤ (1 + B) * A := by nlinarith
    have hp := pow_le_pow_left₀ (show 0 ≤ A + B by linarith) hle 2
    nlinarith
  have hbudget := halving_blocks_radius_budget length radius N q (x ^ α) F C A B
    hq hq1 (Real.rpow_nonneg hx α) hC (by linarith) hB hlen hrad
  have hscaled := mul_le_mul_of_nonneg_left hAB
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg hx α) hC) hS)
  dsimp [A, S] at hbudget hscaled
  nlinarith

end MatedCRT.Sec7
