import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicDelayedRadius

/-! Concatenating the shell-radius sums of dyadic crossing blocks. -/

namespace MatedCRT.Sec7

/-- The sums over consecutive crossing blocks concatenate to the sum of all
delayed radii up to the final crossing time. -/
theorem sum_delayed_radii_over_crossing_blocks
    (r : ℕ → ℝ) (times : ℕ → ℕ) (h0 : times 0 = 0)
    (hmono : ∀ j, times j ≤ times (j + 1)) (N : ℕ) :
    (∑ j ∈ Finset.range N, ∑ k ∈ Finset.range (times (j + 1) - times j),
      r (times j + k + 1)) = ∑ k ∈ Finset.range (times N), r (k + 1) := by
  induction N with
  | zero => simp [h0]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have heq : times (N + 1) = times N + (times (N + 1) - times N) := by
      have := hmono N
      omega
    rw [heq, Finset.sum_range_add]
    simp only [Nat.add_sub_cancel_left]

/-- The radius after each shell is controlled by a summable geometric term
and the accumulated floor, with skipped levels contributing nothing. -/
theorem delayed_crossing_radii_budget
    (O r u : ℕ → ℝ) (times : ℕ → ℕ) (N : ℕ) (S K α F s q C A B : ℝ)
    (hS : 0 ≤ S) (hK : 0 ≤ K) (hα : 0 ≤ α) (hF : 0 ≤ F) (hs : 0 ≤ s)
    (hq : q = (1 / 2 : ℝ) ^ α) (hq1 : q < 1)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h0 : times 0 = 0) (hmono : ∀ j, times j ≤ times (j + 1))
    (hstart : ∀ j, O (times j) ≤ S * (1 / 2 : ℝ) ^ j)
    (hactive : ∀ j k, k < times (j + 1) - times j →
      S * (1 / 2 : ℝ) ^ (j + 1) < O (times j + k))
    (hstep : ∀ j k, k < times (j + 1) - times j →
      O (times j + k + 1) ≤
        (1 - s / (1 + |Real.log (u (times j + k))|) ^ 2) * O (times j + k))
    (hr : ∀ n, r (n + 1) ≤ max ((O n * K) ^ α) F)
    (hlen : ∀ j < N, ((times (j + 1) - times j : ℕ) : ℝ) ≤ C * (A + B * (j : ℝ)) ^ 2) :
    (∑ k ∈ Finset.range (times N), r (k + 1)) ≤
      (S * K) ^ α * C * ((A + B) ^ 2 *
        ∑' j : ℕ, ((j : ℝ) + 1) ^ 2 * q ^ j) + F * (times N : ℝ) := by
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hR : 0 ≤ (S * K) ^ α := Real.rpow_nonneg (mul_nonneg hS hK) α
  have hbound := delayed_radius_le_dyadic_block_envelope O r u times S K α F s
    hS hK hα hF hs hstart hactive hstep hr
  have hbudget := crossing_blocks_radius_budget times (fun j k => r (times j + k + 1))
    N q ((S * K) ^ α) F C A B hq0 hq1 hR hC hA hB h0 hmono hlen
    (fun j _ k hk => by simpa [hq] using hbound j k hk)
  rw [sum_delayed_radii_over_crossing_blocks r times h0 hmono N] at hbudget
  exact hbudget

end MatedCRT.Sec7
