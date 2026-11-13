import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The parameter regime of the exit-time lower tail (proof of BG20 Lemma 6.9)

The proof of BG20 Lemma 6.9 compares the embedded walk, run for `K := ⌊δ^{-(2-ζ)(ℓ-1)}⌋` successive exits from balls
of radius `q := δ^ℓ`, with a planar Brownian motion. With cells of diameter at most `c` and a comparison tolerance
`κ`, the walk event becomes a Brownian event with displacement `a := δ - c - 2κ` before the `K`-th displacement time
of size `r₂ := 2(2q + 6c) + 3κ`. The Brownian estimate (Lemma 6.8, scaled by `a`) applies at the ratio `r := r₂ / a`
with `⌊r^{-(2-ζ/2)}⌋` displacement times. This file proves the real-number inequalities of that regime, for
`c, κ ≤ δ^ℓ / 100`:

* `displacement_ge`: `a ≥ 0.97 δ`;
* `stepScale_le`, `stepScale_pos`: `0 < r₂ ≤ 4.15 δ^ℓ`;
* `stepRatio_le`: `r₂ / a ≤ 5 δ^{ℓ-1}`;
* `floor_le_floor_rpow`: `⌊δ^{-(2-ζ)(ℓ-1)}⌋ ≤ ⌊r^{-(2-ζ/2)}⌋` for `0 < r ≤ 5 δ^{ℓ-1}` once `δ^{-ζ(ℓ-1)/2} ≥ 25`;
* `five_mul_rpow_lt_one`: then also `5 δ^{ℓ-1} < 1`, so `r < 1`;
* `exists_small_rpow_neg_ge`: `δ^{-x} ≥ 25` for all small `δ > 0` (`x > 0`);
* `stepScale_regime`: the four facts used by the assembly, together.
-/

namespace MatedCRT.StepScaleRegime

/-- `δ^ℓ ≤ δ` for `0 < δ ≤ 1` and `ℓ ≥ 1`. -/
lemma rpow_le_self_of_one_le {δ ℓ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hℓ : 1 ≤ ℓ) : δ ^ ℓ ≤ δ := by
  have h := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hℓ
  rwa [Real.rpow_one] at h

/-- The displacement after the comparison losses: `δ - c - 2κ ≥ 0.97 δ` when `c, κ ≤ δ^ℓ / 100`. -/
theorem displacement_ge {δ ℓ c κ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hℓ : 1 ≤ ℓ) (hc : c ≤ δ ^ ℓ / 100)
    (hκ : κ ≤ δ ^ ℓ / 100) : 97 / 100 * δ ≤ δ - c - 2 * κ := by
  have h := rpow_le_self_of_one_le hδ0 hδ1 hℓ
  linarith

/-- The Brownian displacement scale: `2(2δ^ℓ + 6c) + 3κ ≤ 4.15 δ^ℓ` when `c, κ ≤ δ^ℓ / 100`. -/
theorem stepScale_le {δ ℓ c κ : ℝ} (hc : c ≤ δ ^ ℓ / 100) (hκ : κ ≤ δ ^ ℓ / 100) :
    2 * (2 * δ ^ ℓ + 6 * c) + 3 * κ ≤ 415 / 100 * δ ^ ℓ := by
  linarith

/-- The Brownian displacement scale is positive. -/
theorem stepScale_pos {δ ℓ c κ : ℝ} (hδ0 : 0 < δ) (hc0 : 0 ≤ c) (hκ0 : 0 ≤ κ) :
    0 < 2 * (2 * δ ^ ℓ + 6 * c) + 3 * κ := by
  have h := Real.rpow_pos_of_pos hδ0 ℓ
  linarith

/-- The scale ratio: `(2(2δ^ℓ + 6c) + 3κ) / (δ - c - 2κ) ≤ 5 δ^{ℓ-1}` when `c, κ ≤ δ^ℓ / 100`. -/
theorem stepRatio_le {δ ℓ c κ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hℓ : 1 ≤ ℓ) (hc : c ≤ δ ^ ℓ / 100)
    (hκ : κ ≤ δ ^ ℓ / 100) :
    (2 * (2 * δ ^ ℓ + 6 * c) + 3 * κ) / (δ - c - 2 * κ) ≤ 5 * δ ^ (ℓ - 1) := by
  have ha := displacement_ge hδ0 hδ1 hℓ hc hκ
  have hapos : 0 < δ - c - 2 * κ := by linarith
  rw [div_le_iff₀ hapos]
  have h1 : δ ^ (ℓ - 1) * δ = δ ^ ℓ := by
    rw [Real.rpow_sub_one hδ0.ne']
    field_simp
  have h2 : 0 ≤ δ ^ (ℓ - 1) := Real.rpow_nonneg hδ0.le _
  have h3 : δ ^ (ℓ - 1) * (97 / 100 * δ) ≤ δ ^ (ℓ - 1) * (δ - c - 2 * κ) :=
    mul_le_mul_of_nonneg_left ha h2
  have h3' : 97 / 100 * δ ^ ℓ ≤ δ ^ (ℓ - 1) * (δ - c - 2 * κ) := by
    rw [show δ ^ (ℓ - 1) * (97 / 100 * δ) = 97 / 100 * (δ ^ (ℓ - 1) * δ) by ring, h1] at h3
    exact h3
  have h4 := stepScale_le (δ := δ) (ℓ := ℓ) hc hκ
  have h5 : 0 ≤ δ ^ ℓ := Real.rpow_nonneg hδ0.le _
  have h6 : 5 * δ ^ (ℓ - 1) * (δ - c - 2 * κ) = 5 * (δ ^ (ℓ - 1) * (δ - c - 2 * κ)) := by ring
  rw [h6]
  linarith

/-- From `δ^{-x} ≥ 25` to `δ^x ≤ 1/25`. -/
lemma rpow_le_of_le_rpow_neg {δ x : ℝ} (hδ0 : 0 < δ) (h : 25 ≤ δ ^ (-x)) : δ ^ x ≤ 1 / 25 := by
  rw [Real.rpow_neg hδ0.le] at h
  have hpos : 0 < δ ^ x := Real.rpow_pos_of_pos hδ0 x
  have h1 := mul_le_mul_of_nonneg_left h hpos.le
  rw [mul_inv_cancel₀ hpos.ne'] at h1
  linarith

/-- **Floor comparison.** If `0 < r ≤ 5 δ^{ℓ-1}` and `δ^{-ζ(ℓ-1)/2} ≥ 25` with `0 ≤ ζ ≤ 4`, then
`⌊δ^{-(2-ζ)(ℓ-1)}⌋ ≤ ⌊r^{-(2-ζ/2)}⌋`. -/
theorem floor_le_floor_rpow {δ ℓ ζ r : ℝ} (hδ0 : 0 < δ) (hζ0 : 0 ≤ ζ) (hζ4 : ζ ≤ 4)
    (hsmall : 25 ≤ δ ^ (-(ζ * (ℓ - 1) / 2))) (hr0 : 0 < r) (hr : r ≤ 5 * δ ^ (ℓ - 1)) :
    ⌊δ ^ (-((2 - ζ) * (ℓ - 1)))⌋₊ ≤ ⌊r ^ (-(2 - ζ / 2))⌋₊ := by
  apply Nat.floor_le_floor
  have he0 : -(2 - ζ / 2) ≤ 0 := by linarith
  have s1 : (5 * δ ^ (ℓ - 1)) ^ (-(2 - ζ / 2)) ≤ r ^ (-(2 - ζ / 2)) :=
    Real.rpow_le_rpow_of_nonpos hr0 hr he0
  have hd1 : 0 ≤ δ ^ (ℓ - 1) := Real.rpow_nonneg hδ0.le _
  have s2 : (5 * δ ^ (ℓ - 1)) ^ (-(2 - ζ / 2)) =
      (5 : ℝ) ^ (-(2 - ζ / 2)) * δ ^ ((ℓ - 1) * -(2 - ζ / 2)) := by
    rw [Real.mul_rpow (by norm_num) hd1, ← Real.rpow_mul hδ0.le]
  have s3 : δ ^ (-((2 - ζ) * (ℓ - 1))) =
      δ ^ ((ℓ - 1) * -(2 - ζ / 2)) * δ ^ (ζ * (ℓ - 1) / 2) := by
    rw [← Real.rpow_add hδ0]
    congr 1
    ring
  have s4 := rpow_le_of_le_rpow_neg hδ0 hsmall
  have s5 : 1 / 25 ≤ (5 : ℝ) ^ (-(2 - ζ / 2)) := by
    rw [Real.rpow_neg (by norm_num)]
    have h52 : (5 : ℝ) ^ (2 - ζ / 2) ≤ 25 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 5)
        (show 2 - ζ / 2 ≤ (2 : ℝ) by linarith)
      rw [Real.rpow_two] at h
      norm_num at h
      exact h
    rw [one_div]
    exact inv_anti₀ (Real.rpow_pos_of_pos (by norm_num) _) h52
  have hD : 0 ≤ δ ^ ((ℓ - 1) * -(2 - ζ / 2)) := Real.rpow_nonneg hδ0.le _
  rw [s3]
  calc δ ^ ((ℓ - 1) * -(2 - ζ / 2)) * δ ^ (ζ * (ℓ - 1) / 2)
      ≤ δ ^ ((ℓ - 1) * -(2 - ζ / 2)) * (5 : ℝ) ^ (-(2 - ζ / 2)) :=
        mul_le_mul_of_nonneg_left (s4.trans s5) hD
    _ = (5 * δ ^ (ℓ - 1)) ^ (-(2 - ζ / 2)) := by rw [s2]; ring
    _ ≤ r ^ (-(2 - ζ / 2)) := s1

/-- If `δ^{-ζ(ℓ-1)/2} ≥ 25` with `0 < δ ≤ 1`, `ℓ ≥ 1` and `ζ ≤ 2`, then `5 δ^{ℓ-1} < 1`. -/
theorem five_mul_rpow_lt_one {δ ℓ ζ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hℓ : 1 ≤ ℓ) (hζ2 : ζ ≤ 2)
    (hsmall : 25 ≤ δ ^ (-(ζ * (ℓ - 1) / 2))) : 5 * δ ^ (ℓ - 1) < 1 := by
  have hx : ζ * (ℓ - 1) / 2 ≤ ℓ - 1 := by
    have := mul_le_mul_of_nonneg_right hζ2 (show (0 : ℝ) ≤ ℓ - 1 by linarith)
    linarith
  have h1 := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hx
  have h2 := rpow_le_of_le_rpow_neg hδ0 hsmall
  linarith

/-- For `x > 0`, `δ^{-x} ≥ 25` for every `δ` in some interval `(0, δ₁]`. -/
theorem exists_small_rpow_neg_ge {x : ℝ} (hx : 0 < x) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ → 25 ≤ δ ^ (-x) := by
  refine ⟨(1 / 25 : ℝ) ^ x⁻¹, Real.rpow_pos_of_pos (by norm_num) _, fun δ hδ0 hδ => ?_⟩
  have h1 : δ ^ x ≤ 1 / 25 :=
    calc δ ^ x ≤ ((1 / 25 : ℝ) ^ x⁻¹) ^ x := Real.rpow_le_rpow hδ0.le hδ hx.le
      _ = 1 / 25 := Real.rpow_inv_rpow (by norm_num) hx.ne'
  have hpos : 0 < δ ^ x := Real.rpow_pos_of_pos hδ0 x
  rw [Real.rpow_neg hδ0.le]
  have h2 := inv_anti₀ hpos h1
  norm_num at h2
  exact h2

/-- **The regime of the comparison.** For `0 < δ < 1`, `ℓ > 1`, `0 < ζ < 1`, `0 ≤ c, κ ≤ δ^ℓ / 100` and
`δ^{-ζ(ℓ-1)/2} ≥ 25`, the displacement `a := δ - c - 2κ` is positive, the ratio `r := (2(2δ^ℓ + 6c) + 3κ) / a`
lies in `(0, 1)`, and `⌊δ^{-(2-ζ)(ℓ-1)}⌋ ≤ ⌊r^{-(2-ζ/2)}⌋`. -/
theorem stepScale_regime {δ ℓ ζ c κ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hℓ : 1 < ℓ) (hζ0 : 0 < ζ)
    (hζ1 : ζ < 1) (hc0 : 0 ≤ c) (hc : c ≤ δ ^ ℓ / 100) (hκ0 : 0 ≤ κ) (hκ : κ ≤ δ ^ ℓ / 100)
    (hsmall : 25 ≤ δ ^ (-(ζ * (ℓ - 1) / 2))) :
    0 < δ - c - 2 * κ ∧ 0 < (2 * (2 * δ ^ ℓ + 6 * c) + 3 * κ) / (δ - c - 2 * κ) ∧
      (2 * (2 * δ ^ ℓ + 6 * c) + 3 * κ) / (δ - c - 2 * κ) < 1 ∧
      ⌊δ ^ (-((2 - ζ) * (ℓ - 1)))⌋₊ ≤
        ⌊((2 * (2 * δ ^ ℓ + 6 * c) + 3 * κ) / (δ - c - 2 * κ)) ^ (-(2 - ζ / 2))⌋₊ := by
  have ha := displacement_ge hδ0 hδ1.le hℓ.le hc hκ
  have hapos : 0 < δ - c - 2 * κ := by linarith
  have hr0 : 0 < (2 * (2 * δ ^ ℓ + 6 * c) + 3 * κ) / (δ - c - 2 * κ) :=
    div_pos (stepScale_pos hδ0 hc0 hκ0) hapos
  have hr := stepRatio_le hδ0 hδ1.le hℓ.le hc hκ
  have h5 := five_mul_rpow_lt_one hδ0 hδ1.le hℓ.le (by linarith) hsmall
  exact ⟨hapos, hr0, lt_of_le_of_lt hr h5,
    floor_le_floor_rpow hδ0 hζ0.le (by linarith) hsmall hr0 hr⟩

end MatedCRT.StepScaleRegime
