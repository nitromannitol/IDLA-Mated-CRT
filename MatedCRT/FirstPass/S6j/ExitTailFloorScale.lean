import MatedCRT.FirstPass.S6j.StepScaleRegime

/-!
# Comparison of the numbers of displacement times in the proof of BG20 Lemma 6.10

In the Brownian estimate `(6.22)` with exponent `2 + ζ`, `ζ = 1/2`, and step ratio `δ/16`, the number of
displacement times `⌊(δ/16)^{-(2+ζ)}⌋` is at most the number `⌊δ^{-3}⌋` of successive exits of the walk once `δ` is
small, because `16^{5/2} = 1024 ≤ δ^{-1/2}` for `δ ≤ 2^{-20}`.
-/

namespace MatedCRT.ExitTailFloorScale

/-- For `δ` small, `⌊(δ/16)^{-5/2}⌋ ≤ ⌊δ^{-3}⌋`. -/
theorem exists_small_floor_le :
    ∃ δ₂ : ℝ, 0 < δ₂ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₂ →
      ⌊(δ / 16) ^ (-(2 + 1 / 2 : ℝ))⌋₊ ≤ ⌊δ ^ (-3 : ℝ)⌋₊ := by
  refine ⟨(1 / 1024 : ℝ) ^ 2, by positivity, fun δ hδ0 hδ => Nat.floor_le_floor ?_⟩
  have hsq : Real.sqrt δ ≤ 1 / 1024 := by
    calc Real.sqrt δ ≤ Real.sqrt ((1 / 1024 : ℝ) ^ 2) := Real.sqrt_le_sqrt hδ
      _ = 1 / 1024 := Real.sqrt_sq (by norm_num)
  have hspos : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ0
  have hδeq : δ = Real.sqrt δ ^ 2 := (Real.sq_sqrt hδ0.le).symm
  set u := Real.sqrt δ with hu
  have h1 : (δ / 16) ^ (-(2 + 1 / 2 : ℝ)) = 1024 * u ^ (-(5 : ℝ)) := by
    have : δ / 16 = (u / 4) ^ 2 := by rw [hδeq]; ring
    rw [this, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    rw [show ((2 : ℕ) : ℝ) * (-(2 + 1 / 2 : ℝ)) = -5 by norm_num, Real.div_rpow hspos.le (by norm_num),
      Real.rpow_neg hspos.le, Real.rpow_neg (by norm_num)]
    have h4 : (4 : ℝ) ^ (5 : ℝ) = 1024 := by
      rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rw [h4]
    field_simp
  have h2 : δ ^ (-3 : ℝ) = u ^ (-(6 : ℝ)) := by
    rw [hδeq, ← Real.rpow_natCast, ← Real.rpow_mul hspos.le]
    norm_num
  rw [h1, h2]
  have h3 : u ^ (-(6 : ℝ)) = u ^ (-(5 : ℝ)) * u⁻¹ := by
    rw [show -(6 : ℝ) = -(5 : ℝ) + (-1 : ℝ) by norm_num, Real.rpow_add hspos, Real.rpow_neg_one]
  rw [h3]
  have h5 : 0 < u ^ (-(5 : ℝ)) := Real.rpow_pos_of_pos hspos _
  have h6 : (1024 : ℝ) ≤ u⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hspos]
    simpa using hsq
  nlinarith

end MatedCRT.ExitTailFloorScale
