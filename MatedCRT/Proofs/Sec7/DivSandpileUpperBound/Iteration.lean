import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! Deterministic estimates for the shell iteration in Proposition 7.1. -/

namespace MatedCRT.Sec7

/-- A nonnegative sequence contracting by a fixed factor has geometric decay. -/
theorem shell_maximum_le_geometric (O : ℕ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hstep : ∀ k, O (k + 1) ≤ q * O k) (n : ℕ) :
    O n ≤ O 0 * q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      O (n + 1) ≤ q * O n := hstep n
      _ ≤ q * (O 0 * q ^ n) := mul_le_mul_of_nonneg_left ih hq
      _ = O 0 * q ^ (n + 1) := by rw [pow_succ]; ring

/-- The total radius is bounded when each shell has a geometric majorant. -/
theorem shell_radii_sum_le (r : ℕ → ℝ) (A q : ℝ) (hA : 0 ≤ A)
    (hq : 0 ≤ q) (hq1 : q < 1) (n : ℕ)
    (hr : ∀ k < n, r k ≤ A * q ^ k) :
    ∑ k ∈ Finset.range n, r k ≤ A / (1 - q) := by
  calc
    ∑ k ∈ Finset.range n, r k ≤ ∑ k ∈ Finset.range n, A * q ^ k := by
      exact Finset.sum_le_sum fun k hk => hr k (Finset.mem_range.mp hk)
    _ = A * ∑ k ∈ Finset.range n, q ^ k := by rw [Finset.mul_sum]
    _ ≤ A * (1 - q)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact (summable_geometric_of_lt_one hq hq1).sum_le_tsum (Finset.range n)
        (fun k _ => pow_nonneg hq k) |>.trans_eq (tsum_geometric_of_lt_one hq hq1)
    _ = A / (1 - q) := by rw [div_eq_mul_inv]

/-- The radius indexed by `k + 1` is controlled by the maximum at index `k`. -/
theorem shell_shifted_radii_sum_le (r : ℕ → ℝ) (A q : ℝ) (hA : 0 ≤ A)
    (hq : 0 ≤ q) (hq1 : q < 1) (n : ℕ)
    (hr : ∀ k < n, r (k + 1) ≤ A * q ^ k) :
    ∑ k ∈ Finset.range (n + 1), r k ≤ r 0 + A / (1 - q) := by
  rw [Finset.sum_range_succ']
  simpa [add_comm] using add_le_add_left
    (shell_radii_sum_le (fun k => r (k + 1)) A q hA hq hq1 n hr) (r 0)

/-- A path whose odometer increases by `d` at every edge has length at most its total
odometer increase divided by `d`. This is the arithmetic used in Step 3. -/
theorem increasing_path_length_bound (u : ℕ → ℝ) (d : ℝ) (hd : 0 < d) (n : ℕ)
    (hstep : ∀ k < n, u k + d ≤ u (k + 1)) :
    (n : ℝ) ≤ (u n - u 0) / d := by
  have h : ∀ k ≤ n, u 0 + (k : ℝ) * d ≤ u k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hprev := ih (by omega)
      have hnext := hstep k (by omega)
      push_cast
      nlinarith
  apply (le_div_iff₀ hd).2
  linarith [h n (le_refl n)]

end MatedCRT.Sec7
