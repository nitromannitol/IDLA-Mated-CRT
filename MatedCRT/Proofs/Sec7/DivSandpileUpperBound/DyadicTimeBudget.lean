import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicLevelBlocks

/-! Accumulated lengths of dyadic shell blocks. -/

namespace MatedCRT.Sec7

/-- For increasing crossing times starting at zero, the sum of block lengths
is the final crossing time. This includes zero-length skipped levels. -/
theorem sum_crossing_block_lengths (times : ℕ → ℕ) (h0 : times 0 = 0)
    (hmono : ∀ j, times j ≤ times (j + 1)) (N : ℕ) :
    (∑ j ∈ Finset.range N, ((times (j + 1) - times j : ℕ) : ℝ)) = times N := by
  have ht := Finset.sum_range_tsub (monotone_nat_of_le_succ hmono) N
  have ht' : (∑ j ∈ Finset.range N, (times (j + 1) - times j)) = times N := by
    simpa [h0] using ht
  exact_mod_cast ht'

/-- A uniform bound for each block sums to a bound for the time at which the
last level is crossed. -/
theorem crossing_time_le_sum_block_bounds (times : ℕ → ℕ) (bound : ℕ → ℝ)
    (h0 : times 0 = 0) (hmono : ∀ j, times j ≤ times (j + 1))
    (hlen : ∀ j, ((times (j + 1) - times j : ℕ) : ℝ) ≤ bound j) (N : ℕ) :
    (times N : ℝ) ≤ ∑ j ∈ Finset.range N, bound j := by
  rw [← sum_crossing_block_lengths times h0 hmono N]
  exact Finset.sum_le_sum (fun j _ => hlen j)

/-- The geometric part of the shell-radius budget is summable, while the
radius floor contributes precisely the final crossing time times the floor. -/
theorem crossing_blocks_radius_budget
    (times : ℕ → ℕ) (radius : ℕ → ℕ → ℝ) (N : ℕ)
    (q R F C A B : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h0 : times 0 = 0) (hmono : ∀ j, times j ≤ times (j + 1))
    (hlen : ∀ j < N, ((times (j + 1) - times j : ℕ) : ℝ) ≤ C * (A + B * (j : ℝ)) ^ 2)
    (hrad : ∀ j < N, ∀ k < times (j + 1) - times j,
      radius j k ≤ R * q ^ j + F) :
    (∑ j ∈ Finset.range N, ∑ k ∈ Finset.range (times (j + 1) - times j), radius j k) ≤
      R * C * ((A + B) ^ 2 * ∑' j : ℕ, ((j : ℝ) + 1) ^ 2 * q ^ j) +
        F * (times N : ℝ) := by
  have h := halving_blocks_radius_budget (fun j => times (j + 1) - times j)
    radius N q R F C A B hq hq1 hR hC hA hB hlen hrad
  rw [sum_crossing_block_lengths times h0 hmono N] at h
  exact h

end MatedCRT.Sec7
