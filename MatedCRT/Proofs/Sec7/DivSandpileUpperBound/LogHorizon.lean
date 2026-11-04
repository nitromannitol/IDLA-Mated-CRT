import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.PolylogBudget

/-! Explicit polylogarithmic horizons for repeated shell halving. -/

namespace MatedCRT.Sec7

/-- The number of steps in one halving block and the number of blocks can be
chosen with a product bounded by a cubic logarithmic loss. -/
theorem exists_cubic_log_halving_horizon (a s C : ℝ) (hs : 0 < s) (hC : 0 ≤ C) :
    ∃ M N : ℕ,
      C * (1 + |Real.log a|) < M ∧
      2 * (1 + |Real.log a|) ^ 2 < (N : ℝ) * s ∧
      ((M * N : ℕ) : ℝ) ≤
        (C + 2) * (2 / s + 2) * (1 + |Real.log a|) ^ 3 := by
  let L := 1 + |Real.log a|
  have hL : 1 ≤ L := by dsimp [L]; linarith [abs_nonneg (Real.log a)]
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  let M : ℕ := ⌈C * L⌉₊ + 1
  let N : ℕ := ⌈2 * L ^ 2 / s⌉₊ + 1
  have hm0 : 0 ≤ C * L := mul_nonneg hC (by linarith)
  have hn0 : 0 ≤ 2 * L ^ 2 / s := by positivity
  have hmlo := Nat.le_ceil (C * L)
  have hmhi := Nat.ceil_lt_add_one hm0
  have hnlo := Nat.le_ceil (2 * L ^ 2 / s)
  have hnhi := Nat.ceil_lt_add_one hn0
  have hMlo : C * L < (M : ℝ) := by dsimp [M]; push_cast; linarith
  have hNlo : 2 * L ^ 2 < (N : ℝ) * s := by
    have h : 2 * L ^ 2 / s < (N : ℝ) := by dsimp [N]; push_cast; linarith
    exact (div_lt_iff₀ hs).1 h
  have hMhi : (M : ℝ) ≤ (C + 2) * L := by dsimp [M]; push_cast; nlinarith
  have hNhi : (N : ℝ) ≤ (2 / s + 2) * L ^ 2 := by
    dsimp [N]
    push_cast
    have hnhi' : (⌈2 * L ^ 2 / s⌉₊ : ℝ) < (2 / s) * L ^ 2 + 1 := by
      convert hnhi using 1
      ring
    nlinarith
  have hmul := mul_le_mul hMhi hNhi (Nat.cast_nonneg N)
    (by positivity : 0 ≤ (C + 2) * L)
  refine ⟨M, N, hMlo, hNlo, ?_⟩
  push_cast
  nlinarith

end MatedCRT.Sec7
