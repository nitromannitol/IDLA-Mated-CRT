import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicShellSum

/-! An explicit horizon for finitely many dyadic level crossings. -/

namespace MatedCRT.Sec7

/-- Quadratic block-length bounds give a cubic bound in the number of
levels, with the logarithmic radius scale retained explicitly. -/
theorem crossing_time_le_quadratic_level_horizon
    (times : ℕ → ℕ) (N : ℕ) (C A B : ℝ)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h0 : times 0 = 0) (hmono : ∀ j, times j ≤ times (j + 1))
    (hlen : ∀ j, ((times (j + 1) - times j : ℕ) : ℝ) ≤
      C * (A + B * (j : ℝ)) ^ 2) :
    (times N : ℝ) ≤ (N : ℝ) * C * (A + B * (N : ℝ)) ^ 2 := by
  have hsum := crossing_time_le_sum_block_bounds times
    (fun j => C * (A + B * (j : ℝ)) ^ 2) h0 hmono hlen N
  have hpoint : ∀ j ∈ Finset.range N,
      C * (A + B * (j : ℝ)) ^ 2 ≤ C * (A + B * (N : ℝ)) ^ 2 := by
    intro j hj
    have hjN : (j : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hj))
    have hle : A + B * (j : ℝ) ≤ A + B * (N : ℝ) := by nlinarith
    have hn : 0 ≤ A + B * (j : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn hle 2) hC
  calc
    (times N : ℝ) ≤ ∑ j ∈ Finset.range N, C * (A + B * (j : ℝ)) ^ 2 := hsum
    _ ≤ ∑ _j ∈ Finset.range N, C * (A + B * (N : ℝ)) ^ 2 :=
      Finset.sum_le_sum hpoint
    _ = (N : ℝ) * C * (A + B * (N : ℝ)) ^ 2 := by simp; ring

end MatedCRT.Sec7
