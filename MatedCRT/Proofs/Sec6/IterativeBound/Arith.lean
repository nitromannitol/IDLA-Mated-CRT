import MatedCRT.Steps.Sec6.IterativeBound

/-!
# Lemma 6.10: real inequalities for the radius and failure budgets (Steps 1, 2, 4)

* `one_add_abs_log_sq_le`: `(1 + |log r|)² ≤ 64 r^{-1/4}` on `(0, 1]`, so the absorption rate
  `s₄ (1 + |log r|)⁻²` of Lemma 6.9 (E-A10 (b)) is at least `(s₄/64) r^{1/4}`.
* `potential_step`: one round with `x₁ ≤ (1 - p)^a x` and `p ≥ c₄ x^{1/4}` lowers `A x^{1/2}` by `2x`, for
  `A = 8/(a c₄)`.
* `exp_neg_le_factorial_div`: `e^{-y} ≤ k!/y^k`.
-/

namespace MatedCRT

namespace IterativeBound

theorem one_add_abs_log_sq_le {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (1 + |Real.log r|) ^ 2 ≤ 64 * r ^ (-(1 / 4 : ℝ)) := by
  have hlog : Real.log r ≤ 0 := Real.log_nonpos hr0.le hr1
  have he : r ^ (-(1 / 4 : ℝ)) = Real.exp (-Real.log r / 8) ^ 2 := by
    rw [Real.rpow_def_of_pos hr0, sq, ← Real.exp_add]
    congr 1
    ring
  rw [abs_of_nonpos hlog, he]
  have h8 : -Real.log r / 8 + 1 ≤ Real.exp (-Real.log r / 8) := Real.add_one_le_exp _
  have h0 : 0 ≤ -Real.log r / 8 + 1 := by linarith
  have := mul_le_mul h8 h8 h0 (h0.trans h8)
  nlinarith

/-- The absorption rate of Lemma 6.9 in power form: `s (1 + |log r|)⁻² ≥ (s/64) r^{1/4}` on `(0, 1]`. -/
theorem div_one_add_abs_log_sq_ge {r s : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hs : 0 ≤ s) :
    s / 64 * r ^ (1 / 4 : ℝ) ≤ s / (1 + |Real.log r|) ^ 2 := by
  have hL : 0 < (1 + |Real.log r|) ^ 2 := by positivity
  have h := one_add_abs_log_sq_le hr0 hr1
  have hr4 : 0 < r ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hr0 _
  have hinv : r ^ (-(1 / 4 : ℝ)) * r ^ (1 / 4 : ℝ) = 1 := by
    rw [← Real.rpow_add hr0]
    norm_num
  rw [le_div_iff₀ hL]
  calc s / 64 * r ^ (1 / 4 : ℝ) * (1 + |Real.log r|) ^ 2
      ≤ s / 64 * r ^ (1 / 4 : ℝ) * (64 * r ^ (-(1 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = s * (r ^ (-(1 / 4 : ℝ)) * r ^ (1 / 4 : ℝ)) := by ring
    _ = s := by rw [hinv, mul_one]

theorem half_le_one_sub_exp_neg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t / 2 ≤ 1 - Real.exp (-t) := by
  have hE := Real.add_one_le_exp t
  have hpos := Real.exp_pos (-t)
  have hprod : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]
    simp
  have h1 : Real.exp (-t) * (t + 1) ≤ 1 := by
    calc Real.exp (-t) * (t + 1) ≤ Real.exp (-t) * Real.exp t := mul_le_mul_of_nonneg_left hE hpos.le
      _ = 1 := hprod
  nlinarith [mul_nonneg ht0 (sub_nonneg.2 ht1)]

theorem exp_neg_le_factorial_div {y : ℝ} (hy : 0 < y) (k : ℕ) :
    Real.exp (-y) ≤ k.factorial / y ^ k := by
  have h := Real.pow_div_factorial_le_exp y hy.le k
  rw [Real.exp_neg]
  have hyk : 0 < y ^ k / k.factorial := by positivity
  calc (Real.exp y)⁻¹ ≤ (y ^ k / k.factorial)⁻¹ := inv_anti₀ hyk h
    _ = k.factorial / y ^ k := inv_div _ _

/-- **One round lowers the potential** `A x^{1/2}` by `2x` (Step 1, eq:bound-on-radii-sum): if
`x₁ ≤ (1 - p)^a x` with `p ≥ c₄ x^{1/4}`, `0 < a ≤ 1/2` and `0 < x ≤ 1`, then
`A x₁^{1/2} + 2x ≤ A x^{1/2}` for `A = 8/(a c₄)`. -/
theorem potential_step {x x₁ p a c₄ : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hx₁0 : 0 ≤ x₁)
    (ha : 0 < a) (ha1 : a ≤ 1 / 2) (hc₄ : 0 < c₄) (hp : c₄ * x ^ (1 / 4 : ℝ) ≤ p) (hp1 : p < 1)
    (hx₁ : x₁ ≤ (1 - p) ^ a * x) :
    8 / (a * c₄) * x₁ ^ (1 / 2 : ℝ) + 2 * x ≤ 8 / (a * c₄) * x ^ (1 / 2 : ℝ) := by
  have hp0 : 0 ≤ p := le_trans (by positivity) hp
  have h1p : 0 ≤ 1 - p := by linarith
  have hexp : (1 - p) ^ a ≤ Real.exp (-(a * p)) := by
    calc (1 - p) ^ a ≤ Real.exp (-p) ^ a :=
          Real.rpow_le_rpow h1p (by linarith [Real.add_one_le_exp (-p)]) ha.le
      _ = Real.exp (-(a * p)) := by
          rw [← Real.exp_mul]
          ring_nf
  have hx₁' : x₁ ≤ Real.exp (-(a * p)) * x := hx₁.trans (mul_le_mul_of_nonneg_right hexp hx.le)
  have hsq : x₁ ^ (1 / 2 : ℝ) ≤ Real.exp (-(a * p / 2)) * x ^ (1 / 2 : ℝ) := by
    calc x₁ ^ (1 / 2 : ℝ) ≤ (Real.exp (-(a * p)) * x) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hx₁0 hx₁' (by norm_num)
      _ = Real.exp (-(a * p)) ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := Real.mul_rpow (Real.exp_pos _).le hx.le
      _ = Real.exp (-(a * p / 2)) * x ^ (1 / 2 : ℝ) := by
          rw [← Real.exp_mul]
          ring_nf
  have ht : a * p / 4 ≤ 1 - Real.exp (-(a * p / 2)) := by
    have := half_le_one_sub_exp_neg (t := a * p / 2) (by positivity) (by nlinarith)
    linarith
  have hx34 : x ≤ x ^ (1 / 2 : ℝ) * x ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hx]
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ (1 / 2 + 1 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hx hx1 (by norm_num)
  have hA : 0 < 8 / (a * c₄) := by positivity
  have hsx : 0 ≤ x ^ (1 / 2 : ℝ) := by positivity
  have key : 2 * x ≤ 8 / (a * c₄) * x ^ (1 / 2 : ℝ) * (a * p / 4) := by
    have h1 : 8 / (a * c₄) * x ^ (1 / 2 : ℝ) * (a * (c₄ * x ^ (1 / 4 : ℝ)) / 4) ≤
        8 / (a * c₄) * x ^ (1 / 2 : ℝ) * (a * p / 4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have := mul_le_mul_of_nonneg_left hp ha.le
      linarith
    have h2 : 8 / (a * c₄) * x ^ (1 / 2 : ℝ) * (a * (c₄ * x ^ (1 / 4 : ℝ)) / 4) =
        2 * (x ^ (1 / 2 : ℝ) * x ^ (1 / 4 : ℝ)) := by
      field_simp [ha.ne', hc₄.ne']
      ring
    linarith
  have hb := mul_le_mul_of_nonneg_left ht (mul_nonneg hA.le hsx)
  have hc := mul_le_mul_of_nonneg_left hsq hA.le
  nlinarith

end IterativeBound

end MatedCRT
