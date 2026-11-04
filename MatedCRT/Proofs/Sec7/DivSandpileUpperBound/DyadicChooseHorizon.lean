import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicDelayedBootstrap
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.LogHorizon

/-! Choosing the dyadic level and a strictly larger shell horizon. -/

namespace MatedCRT.Sec7

/-- A logarithmic bound on the initial-to-target ratio and on the tested
radius produces a dyadic level and a shell horizon with cubic-log growth. -/
theorem exists_dyadic_level_and_cubic_horizon
    (S B a q s L A C : ℝ) (hS : 0 < S) (hB : 0 < B) (hs : 0 < s)
    (hL : 1 ≤ L) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hratio : Real.log (S / B) ≤ C * L * Real.log 2)
    (hlog : 1 + |Real.log a| ≤ A * L) :
    ∃ N n : ℕ,
      S * (1 / 2 : ℝ) ^ N ≤ B ∧
      (N : ℝ) * (2 / s + 2) *
        (1 + |Real.log a| + |Real.log q| * (N : ℝ)) ^ 2 < n ∧
      (n : ℝ) ≤ (C + 2) * (2 / s + 2) *
        (A + |Real.log q| * (C + 2)) ^ 2 * L ^ 3 + 2 := by
  let N : ℕ := ⌈C * L⌉₊ + 1
  let R : ℝ := 2 / s + 2
  let W : ℝ := A + |Real.log q| * (C + 2)
  let H : ℝ := (N : ℝ) * R * (1 + |Real.log a| + |Real.log q| * (N : ℝ)) ^ 2
  let n : ℕ := ⌈H⌉₊ + 1
  have hCL : 0 ≤ C * L := mul_nonneg hC (by linarith)
  have hceilLow := Nat.le_ceil (C * L)
  have hceilHigh := Nat.ceil_lt_add_one hCL
  have hNlow : C * L ≤ (N : ℝ) := by dsimp [N]; push_cast; linarith
  have hNhigh : (N : ℝ) ≤ (C + 2) * L := by dsimp [N]; push_cast; nlinarith
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hlognonneg : 0 ≤ |Real.log q| := abs_nonneg _
  have hinner : 1 + |Real.log a| + |Real.log q| * (N : ℝ) ≤ W * L := by
    dsimp [W]
    nlinarith [mul_le_mul_of_nonneg_left hNhigh hlognonneg]
  have hsq := pow_le_pow_left₀ (by positivity :
    0 ≤ 1 + |Real.log a| + |Real.log q| * (N : ℝ)) hinner 2
  have hNR : (N : ℝ) * R ≤ (C + 2) * L * R :=
    mul_le_mul_of_nonneg_right hNhigh hR
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hHbound : H ≤ (C + 2) * R * W ^ 2 * L ^ 3 := by
    have hmul := mul_le_mul hNR hsq (sq_nonneg _) (by positivity : 0 ≤ (C + 2) * L * R)
    dsimp [H]
    nlinarith [sq_nonneg L]
  have hnlow : H < (n : ℝ) := by
    have hh := Nat.le_ceil H
    dsimp [n]
    push_cast
    linarith
  have hnhigh : (n : ℝ) ≤ H + 2 := by
    have hh := Nat.ceil_lt_add_one hH
    dsimp [n]
    push_cast
    linarith
  refine ⟨N, n, halving_blocks_reach_threshold S B L C N hS hB hratio hNlow, ?_, ?_⟩
  · exact hnlow
  · dsimp [W, R] at hHbound
    linarith

end MatedCRT.Sec7
