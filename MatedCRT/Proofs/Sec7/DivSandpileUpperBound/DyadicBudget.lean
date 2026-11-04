import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.LogLossSeries

/-! Summing shell radii grouped by successive halvings of the maximum. -/

namespace MatedCRT.Sec7

/-- If the lengths of successive halving blocks have a quadratic logarithmic
bound and the radii decay geometrically between blocks, their total radius is
bounded uniformly in the number of blocks, up to the accumulated radius floor.
The hypotheses on block lengths and radii are kept separate for use with a
first-halving construction. -/
theorem halving_blocks_radius_budget
    (length : ℕ → ℕ) (radius : ℕ → ℕ → ℝ) (N : ℕ)
    (q R F C A B : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hlen : ∀ j < N, (length j : ℝ) ≤ C * (A + B * (j : ℝ)) ^ 2)
    (hrad : ∀ j < N, ∀ k < length j, radius j k ≤ R * q ^ j + F) :
    (∑ j ∈ Finset.range N, ∑ k ∈ Finset.range (length j), radius j k) ≤
      R * C * ((A + B) ^ 2 * ∑' j : ℕ, ((j : ℝ) + 1) ^ 2 * q ^ j) +
        F * ∑ j ∈ Finset.range N, (length j : ℝ) := by
  have hblock : ∀ j < N,
      (∑ k ∈ Finset.range (length j), radius j k) ≤
        (length j : ℝ) * R * q ^ j + F * (length j : ℝ) := by
    intro j hj
    calc
      _ ≤ ∑ _k ∈ Finset.range (length j), (R * q ^ j + F) :=
        Finset.sum_le_sum (fun k hk => hrad j hj k (Finset.mem_range.mp hk))
      _ = _ := by simp; ring
  have hdecay :
      (∑ j ∈ Finset.range N, (length j : ℝ) * R * q ^ j) ≤
        R * C * ∑ j ∈ Finset.range N, (A + B * (j : ℝ)) ^ 2 * q ^ j := by
    calc
      _ ≤ ∑ j ∈ Finset.range N, R * C * ((A + B * (j : ℝ)) ^ 2 * q ^ j) := by
        apply Finset.sum_le_sum
        intro j hj
        have hmul := mul_le_mul_of_nonneg_right (hlen j (Finset.mem_range.mp hj))
          (mul_nonneg hR (pow_nonneg hq j))
        nlinarith
      _ = _ := by rw [Finset.mul_sum]
  have hseries := quadratic_geometric_sum_le hq hq1 hA hB N
  calc
    _ ≤ ∑ j ∈ Finset.range N, ((length j : ℝ) * R * q ^ j + F * (length j : ℝ)) :=
      Finset.sum_le_sum (fun j hj => hblock j (Finset.mem_range.mp hj))
    _ = (∑ j ∈ Finset.range N, (length j : ℝ) * R * q ^ j) +
        F * ∑ j ∈ Finset.range N, (length j : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by
      have hseries' := mul_le_mul_of_nonneg_left hseries (mul_nonneg hR hC)
      linarith

end MatedCRT.Sec7
