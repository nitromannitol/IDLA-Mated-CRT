import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicTimeBudget
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.RadiusChoice

/-! Delayed shell radii within dyadic odometer blocks. -/

namespace MatedCRT.Sec7

/-- Within a block, contraction before its first level crossing keeps the
odometer maximum below its value at the start of the block. -/
theorem odometer_le_block_start
    (O : ℕ → ℝ) (t len : ℕ) (lo s : ℝ) (u : ℕ → ℝ)
    (hlo : 0 ≤ lo) (hs : 0 ≤ s)
    (hactive : ∀ k < len, lo < O (t + k))
    (hstep : ∀ k < len, O (t + k + 1) ≤
      (1 - s / (1 + |Real.log (u (t + k))|) ^ 2) * O (t + k)) :
    ∀ k ≤ len, O (t + k) ≤ O t := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
    have hpos : 0 ≤ O (t + k) := le_trans hlo (hactive k (by omega)).le
    have hrate : 0 ≤ s / (1 + |Real.log (u (t + k))|) ^ 2 := by positivity
    have hmul := mul_nonneg hrate hpos
    have hnext := hstep k (by omega)
    have hprev := ih (by omega)
    simp only [Nat.add_succ] at hnext ⊢
    nlinarith

/-- If shell radii are chosen from the previous maximum, all radii immediately
following a dyadic block are bounded by a geometric term plus the mesh floor.
The initial radius is handled separately in the shell budget. -/
theorem delayed_radius_le_dyadic_block_envelope
    (O r u : ℕ → ℝ) (times : ℕ → ℕ) (S K α F s : ℝ)
    (hS : 0 ≤ S) (hK : 0 ≤ K) (hα : 0 ≤ α) (hF : 0 ≤ F) (hs : 0 ≤ s)
    (hstart : ∀ j, O (times j) ≤ S * (1 / 2 : ℝ) ^ j)
    (hactive : ∀ j k, k < times (j + 1) - times j →
      S * (1 / 2 : ℝ) ^ (j + 1) < O (times j + k))
    (hstep : ∀ j k, k < times (j + 1) - times j →
      O (times j + k + 1) ≤
        (1 - s / (1 + |Real.log (u (times j + k))|) ^ 2) * O (times j + k))
    (hr : ∀ n, r (n + 1) ≤ max ((O n * K) ^ α) F) :
    ∀ j k, k < times (j + 1) - times j →
      r (times j + k + 1) ≤ (S * K) ^ α * ((1 / 2 : ℝ) ^ α) ^ j + F := by
  intro j k hk
  have hlo : 0 ≤ S * (1 / 2 : ℝ) ^ (j + 1) := by positivity
  have hO : 0 ≤ O (times j + k) := le_trans hlo (hactive j k hk).le
  have hblock := odometer_le_block_start O (times j) (times (j + 1) - times j)
    (S * (1 / 2 : ℝ) ^ (j + 1)) s u hlo hs (hactive j) (hstep j) k (Nat.le_of_lt hk)
  have hbase : O (times j + k) * K ≤ (S * (1 / 2 : ℝ) ^ j) * K :=
    mul_le_mul_of_nonneg_right (hblock.trans (hstart j)) hK
  have hp := Real.rpow_le_rpow (mul_nonneg hO hK) hbase hα
  have heq : ((S * (1 / 2 : ℝ) ^ j) * K) ^ α =
      (S * K) ^ α * ((1 / 2 : ℝ) ^ α) ^ j := by
    rw [show (S * (1 / 2 : ℝ) ^ j) * K = (S * K) * (1 / 2 : ℝ) ^ j by ring,
      Real.mul_rpow (mul_nonneg hS hK) (by positivity),
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2) j α,
      mul_comm (j : ℝ) α, Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 1 / 2) α j]
  rw [heq] at hp
  have hterm : 0 ≤ (S * K) ^ α * ((1 / 2 : ℝ) ^ α) ^ j := by positivity
  exact (hr (times j + k)).trans (max_le (by linarith) (by linarith))

end MatedCRT.Sec7
