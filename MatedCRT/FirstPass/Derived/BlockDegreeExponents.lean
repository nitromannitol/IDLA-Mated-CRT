import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Exponents for the block degree estimate

Real-variable estimates used to turn the running-minimum tail of Berestycki–Gwynne (2020), Lemma A.9,
into the block degree estimate (A.43) with polynomially high probability. With
`L = log ε⁻¹`, blocks of `N ≤ ε^{-1/2}` cells, degrees at most `L²` and at most
`m = ε^{-1/4} L²` running-minimum cells for each of four paths:

* `exists_blockError_le`: the error `2 + (2 + L²) · 4m` is at most `ε^{-1/2 + 1/8}` for small `ε`;
* `exists_mul_rpow_neg_mul_exp_le`: the tail `exp(-c m / √N) ≤ exp(-c L²)` beats every power:
  `C ε^{-k} exp(-c L²) ≤ ε` for small `ε`.
-/

open Filter Real Asymptotics

namespace MatedCRT

/-- A property holding for all large `x` holds at `ε⁻¹` for all small `ε > 0`. -/
theorem exists_pos_forall_lt_of_eventually_atTop_inv {P : ℝ → Prop} (h : ∀ᶠ x in atTop, P x) :
    ∃ ε₁ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₁ → P ε⁻¹ := by
  obtain ⟨X, hX⟩ := eventually_atTop.1 h
  have hX1 : 0 < max X 1 := lt_max_of_lt_right one_pos
  refine ⟨(max X 1)⁻¹, inv_pos.2 hX1, fun ε hε hε1 => hX _ ?_⟩
  exact (le_max_left _ _).trans ((lt_inv_comm₀ hX1 hε).2 hε1).le

/-- **The block error exponent.** With `L = log ε⁻¹`, `2 + (2 + L²) · 4 ε^{-1/4} L² ≤ ε^{-1/2 + 1/8}`
for all small `ε > 0`. -/
theorem exists_blockError_le :
    ∃ ε₁ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₁ →
      2 + (2 + Real.log ε⁻¹ ^ 2) * (4 * (ε ^ (-(1 / 4 : ℝ)) * Real.log ε⁻¹ ^ 2)) ≤
        ε ^ (-(1 / 2 : ℝ) + 1 / 8) := by
  have h4 := (isLittleO_log_rpow_rpow_atTop (4 : ℝ) (by norm_num : (0 : ℝ) < 1 / 8)).def
    (by norm_num : (0 : ℝ) < 1 / 32)
  have h2 := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1 / 8)).def
    (by norm_num : (0 : ℝ) < 1 / 32)
  have h38 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 8)).eventually_ge_atTop 4
  obtain ⟨ε₁, hε₁, h⟩ := exists_pos_forall_lt_of_eventually_atTop_inv
    (P := fun x => 2 + (2 + Real.log x ^ 2) * (4 * (x ^ (1 / 4 : ℝ) * Real.log x ^ 2)) ≤
      x ^ (3 / 8 : ℝ))
    ((h4.and (h2.and (h38.and (eventually_gt_atTop (1 : ℝ))))).mono
      fun x ⟨hx4, hx2, hx38, hx1⟩ => by
        have hx0 : 0 < x := by linarith
        have hL : 0 ≤ Real.log x := Real.log_nonneg hx1.le
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hL _),
          abs_of_nonneg (Real.rpow_nonneg hx0.le _)] at hx4 hx2
        have e4 : Real.log x ^ (4 : ℝ) = Real.log x ^ 4 := by
          rw [← Real.rpow_natCast]; norm_num
        have e2 : Real.log x ^ (2 : ℝ) = Real.log x ^ 2 := by
          rw [← Real.rpow_natCast]; norm_num
        rw [e4] at hx4
        rw [e2] at hx2
        have hsplit : x ^ (3 / 8 : ℝ) = x ^ (1 / 4 : ℝ) * x ^ (1 / 8 : ℝ) := by
          rw [← Real.rpow_add hx0]; norm_num
        have hq : 0 ≤ x ^ (1 / 4 : ℝ) := Real.rpow_nonneg hx0.le _
        rw [hsplit] at hx38 ⊢
        nlinarith [mul_le_mul_of_nonneg_left hx4 hq, mul_le_mul_of_nonneg_left hx2 hq])
  refine ⟨ε₁, hε₁, fun ε hε hεε => ?_⟩
  have := h ε hε hεε
  rwa [Real.inv_rpow hε.le, ← Real.rpow_neg hε.le, Real.inv_rpow hε.le, ← Real.rpow_neg hε.le,
    show -(3 / 8 : ℝ) = -(1 / 2) + 1 / 8 by norm_num] at this

/-- **The running-minimum tail beats every power.** For `c > 0` and all real `C, k`, with
`L = log ε⁻¹`, `C ε^{-k} exp(-c L²) ≤ ε` for all small `ε > 0`. -/
theorem exists_mul_rpow_neg_mul_exp_le (C c k : ℝ) (hc : 0 < c) :
    ∃ ε₁ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₁ →
      C * ε ^ (-k) * Real.exp (-(c * Real.log ε⁻¹ ^ 2)) ≤ ε := by
  obtain ⟨T, hT⟩ : ∃ T, T = max 1 ((k + 1 + |Real.log C|) / c) := ⟨_, rfl⟩
  refine ⟨Real.exp (-T), Real.exp_pos _, fun ε hε hεε => ?_⟩
  have hL : T < Real.log ε⁻¹ := by
    have := Real.log_lt_log hε hεε
    rw [Real.log_exp] at this
    rw [Real.log_inv]
    linarith
  have hT1 : 1 ≤ T := hT ▸ le_max_left _ _
  have hT2 : (k + 1 + |Real.log C|) / c ≤ T := hT ▸ le_max_right _ _
  have hεeq : ε = Real.exp (-Real.log ε⁻¹) := by
    rw [Real.log_inv, neg_neg, Real.exp_log hε]
  have hεk : ε ^ (-k) = Real.exp (k * Real.log ε⁻¹) := by
    rw [Real.rpow_def_of_pos hε, Real.log_inv]
    congr 1
    ring
  rcases le_or_gt C 0 with hC | hC
  · have : C * ε ^ (-k) * Real.exp (-(c * Real.log ε⁻¹ ^ 2)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hC (Real.rpow_nonneg hε.le _)) (Real.exp_pos _).le
    linarith
  · rw [hεk, ← Real.exp_log hC, ← Real.exp_add, ← Real.exp_add]
    conv_rhs => rw [hεeq]
    apply Real.exp_le_exp.2
    have hlogC : Real.log C ≤ |Real.log C| := le_abs_self _
    have hL1 : (k + 1 + |Real.log C|) / c < Real.log ε⁻¹ := hT2.trans_lt hL
    rw [div_lt_iff₀ hc] at hL1
    have hL0 : 1 < Real.log ε⁻¹ := hT1.trans_lt hL
    nlinarith [mul_pos (by linarith : (0 : ℝ) < Real.log ε⁻¹)
        (by linarith : (0 : ℝ) < Real.log ε⁻¹ * c - (k + 1 + |Real.log C|)),
      mul_nonneg (abs_nonneg (Real.log C)) (by linarith : (0 : ℝ) ≤ Real.log ε⁻¹ - 1)]

end MatedCRT
