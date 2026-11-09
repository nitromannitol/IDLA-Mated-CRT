import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# LEMMA68 printed 6.9: the one-step contraction and the exponential identity (q2, task fp-S4S6c)

Source: notes/fp-gaps/CHATGPT-lemma68-open-parts.md, Section 3 (uniformity for the printed Lemma 6.9). With the uniform
one-step bound `P(Y_i = 1 | history) ≥ 1/2` (from the uniform Lemma 6.7 with `s₂ = 1/2`), the absorbed count satisfies
`P(∑_{i≤k} Y_i ≤ k/4) ≤ 3^{k/4} (2/3)^k = e^{-s₃ k}` with `s₃ = ¾ log 3 − log 2 > 0`.

This file proves the two algebraic ingredients:
* `one_step`: for `Y ∈ {0,1}`, `E[w · 3^{-Y}] ≤ (2/3) E[w]` whenever `E[w · 1_{Y=1}] ≥ ½ E[w]` (the one-step tower bound);
* `rpow_mul_pow_eq_exp`: `3^{k/4} (2/3)^k = e^{-s₃ k}`, and `s3_pos`: `s₃ > 0` (equivalent to `27 > 16`).
The induction over the walkers and the Markov step `1{∑ Y ≤ k/4} ≤ 3^{k/4} 3^{-∑Y}` are the next step.
-/

open MeasureTheory
open scoped ENNReal

namespace MatedCRT

namespace AbsorbedChernoff

/-- The printed Lemma 6.9 rate `s₃ = ¾ log 3 − log 2`. -/
noncomputable def s3 : ℝ := 3 / 4 * Real.log 3 - Real.log 2

/-- `s₃ > 0`, since `27 > 16`. -/
theorem s3_pos : 0 < s3 := by
  unfold s3
  have h : Real.log 16 < Real.log 27 := Real.log_lt_log (by norm_num) (by norm_num)
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have h27 : Real.log 27 = 3 * Real.log 3 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]
    norm_num
  linarith

/-- The exponential identity `3^{k/4} (2/3)^k = e^{-s₃ k}`. -/
theorem rpow_mul_pow_eq_exp (k : ℕ) :
    (3 : ℝ) ^ ((k : ℝ) / 4) * ((2 : ℝ) / 3) ^ k = Real.exp (-s3 * k) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  rw [show ((2 : ℝ) / 3) ^ k = Real.exp (Real.log (2 / 3)) ^ k by rw [Real.exp_log (by norm_num)]]
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  rw [Real.log_div (by norm_num) (by norm_num), s3]
  ring

/-- Pointwise identity for `Y ∈ {0,1}`: `w · 3^{-Y} + (2 · 3⁻¹) · (w · 1_{Y=1}) = w`. -/
theorem pointwise_identity {Y : ℕ} (hY : Y ≤ 1) (w : ℝ≥0∞) :
    w * (3⁻¹ : ℝ≥0∞) ^ Y + (2 * 3⁻¹) * (w * (if Y = 1 then 1 else 0)) = w := by
  have h3 : (3 : ℝ≥0∞) * 3⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have hsum : (3⁻¹ : ℝ≥0∞) + 2 * 3⁻¹ = 1 := by
    calc (3⁻¹ : ℝ≥0∞) + 2 * 3⁻¹ = 3 * 3⁻¹ := by ring
      _ = 1 := h3
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hY with rfl | rfl
  · simp
  · simp only [pow_one, ↓reduceIte, mul_one]
    calc w * 3⁻¹ + 2 * 3⁻¹ * w = w * (3⁻¹ + 2 * 3⁻¹) := by ring
      _ = w := by rw [hsum, mul_one]

/-- **One-step contraction** (write-up Section 3). If `E[w · 1_{Y=1}] ≥ ½ E[w]` for a `{0,1}`-valued `Y` and `E[w] < ∞`, then
`E[w · 3^{-Y}] ≤ (2/3) E[w]`. -/
theorem one_step {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {w : Ω → ℝ≥0∞} {Y : Ω → ℕ}
    (hwm : Measurable w) (hYm : Measurable Y) (hY : ∀ ω, Y ω ≤ 1) (hfin : ∫⁻ ω, w ω ∂P ≠ ⊤)
    (hstep : 2⁻¹ * ∫⁻ ω, w ω ∂P ≤ ∫⁻ ω, w ω * (if Y ω = 1 then 1 else 0) ∂P) :
    ∫⁻ ω, w ω * (3⁻¹ : ℝ≥0∞) ^ Y ω ∂P ≤ (2 * 3⁻¹) * ∫⁻ ω, w ω ∂P := by
  have hind : Measurable (fun ω => if Y ω = 1 then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_eq_fun hYm measurable_const) measurable_const measurable_const
  have hm1 : Measurable (fun ω => w ω * (3⁻¹ : ℝ≥0∞) ^ Y ω) :=
    hwm.mul ((measurable_from_nat (f := fun n : ℕ => (3⁻¹ : ℝ≥0∞) ^ n)).comp hYm)
  have hm2 : Measurable (fun ω => w ω * (if Y ω = 1 then (1 : ℝ≥0∞) else 0)) := hwm.mul hind
  have hsum : ∫⁻ ω, w ω * (3⁻¹ : ℝ≥0∞) ^ Y ω ∂P + (2 * 3⁻¹) *
      ∫⁻ ω, w ω * (if Y ω = 1 then (1 : ℝ≥0∞) else 0) ∂P = ∫⁻ ω, w ω ∂P := by
    rw [← lintegral_const_mul _ hm2, ← lintegral_add_left hm1]
    exact lintegral_congr fun ω => pointwise_identity (hY ω) (w ω)
  have h2 : (2 : ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have h3 : (3 : ℝ≥0∞) * 3⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have hkey : (2 * 3⁻¹ : ℝ≥0∞) * (2⁻¹ * ∫⁻ ω, w ω ∂P) = 3⁻¹ * ∫⁻ ω, w ω ∂P := by
    calc (2 * 3⁻¹ : ℝ≥0∞) * (2⁻¹ * ∫⁻ ω, w ω ∂P) = (2 * 2⁻¹) * 3⁻¹ * ∫⁻ ω, w ω ∂P := by ring
      _ = 3⁻¹ * ∫⁻ ω, w ω ∂P := by rw [h2, one_mul]
  have hc : (2 * 3⁻¹ : ℝ≥0∞) + 3⁻¹ = 1 := by
    calc (2 * 3⁻¹ : ℝ≥0∞) + 3⁻¹ = 3 * 3⁻¹ := by ring
      _ = 1 := h3
  have h3W : (3⁻¹ : ℝ≥0∞) * ∫⁻ ω, w ω ∂P ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (by norm_num)) hfin
  have hle : (3⁻¹ : ℝ≥0∞) * ∫⁻ ω, w ω ∂P ≤ (2 * 3⁻¹) *
      ∫⁻ ω, w ω * (if Y ω = 1 then (1 : ℝ≥0∞) else 0) ∂P := by
    rw [← hkey]
    exact mul_le_mul_of_nonneg_left hstep (by positivity)
  have h1 : ∫⁻ ω, w ω * (3⁻¹ : ℝ≥0∞) ^ Y ω ∂P + 3⁻¹ * ∫⁻ ω, w ω ∂P ≤
      (2 * 3⁻¹) * ∫⁻ ω, w ω ∂P + 3⁻¹ * ∫⁻ ω, w ω ∂P := by
    calc ∫⁻ ω, w ω * (3⁻¹ : ℝ≥0∞) ^ Y ω ∂P + 3⁻¹ * ∫⁻ ω, w ω ∂P
        ≤ ∫⁻ ω, w ω * (3⁻¹ : ℝ≥0∞) ^ Y ω ∂P + (2 * 3⁻¹) *
            ∫⁻ ω, w ω * (if Y ω = 1 then (1 : ℝ≥0∞) else 0) ∂P :=
          add_le_add le_rfl hle
      _ = ∫⁻ ω, w ω ∂P := hsum
      _ = (2 * 3⁻¹) * ∫⁻ ω, w ω ∂P + 3⁻¹ * ∫⁻ ω, w ω ∂P := by
          rw [← add_mul, hc, one_mul]
  exact ENNReal.le_of_add_le_add_right h3W h1

#print axioms MatedCRT.AbsorbedChernoff.s3_pos
#print axioms MatedCRT.AbsorbedChernoff.rpow_mul_pow_eq_exp
#print axioms MatedCRT.AbsorbedChernoff.one_step

end AbsorbedChernoff

end MatedCRT
