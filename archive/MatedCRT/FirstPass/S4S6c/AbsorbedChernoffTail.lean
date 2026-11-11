import MatedCRT.FirstPass.S4S6c.AbsorbedChernoff69

/-!
# Printed Lemma 6.9: the induction and the Markov tail

Setting. `Y j : Ω → ℕ` with `Y j ≤ 1` is the absorption indicator of walker `j`. The history weight is
`W_j = 3^{-N_j}` with `N_j = ∑_{i<j} Y_i`. The one-step hypothesis `hstep j` states, for the history weight, the integrated
form of the conditional bound `P(Y_j = 1 | history) ≥ 1/2` (from the uniform Lemma 6.7 with `s₂ = 1/2`):
`½ E[W_j] ≤ E[W_j · 1_{Y_j = 1}]`. The tower property converts the conditional bound into this form; it is the only input
from Lemma 6.7.

Results: `weight_integral_le` (`E[W_k] ≤ (2/3)^k`, by induction with `one_step`) and `absorbed_tail_le`
(`P(4 ∑_{i<k} Y_i ≤ k) ≤ e^{-s₃ k}`, by Markov's inequality on `W_k`).
-/

open MeasureTheory Finset
open scoped ENNReal

namespace MatedCRT

namespace AbsorbedChernoff

variable {Ω : Type*}

/-- The history weight `3^{-N_j}` with `N_j = ∑_{i<j} Y_i`. -/
noncomputable def wgt (Y : ℕ → Ω → ℕ) (j : ℕ) (ω : Ω) : ℝ≥0∞ :=
  (3⁻¹ : ℝ≥0∞) ^ (∑ i ∈ range j, Y i ω)

theorem wgt_zero (Y : ℕ → Ω → ℕ) (ω : Ω) : wgt Y 0 ω = 1 := by
  simp [wgt]

theorem wgt_succ (Y : ℕ → Ω → ℕ) (j : ℕ) (ω : Ω) :
    wgt Y (j + 1) ω = wgt Y j ω * (3⁻¹ : ℝ≥0∞) ^ Y j ω := by
  unfold wgt
  rw [Finset.sum_range_succ, pow_add]

theorem wgt_le_one (Y : ℕ → Ω → ℕ) (j : ℕ) (ω : Ω) : wgt Y j ω ≤ 1 := by
  unfold wgt
  exact pow_le_one₀ (by positivity) (ENNReal.inv_le_one.2 (by norm_num))

theorem wgt_measurable [MeasurableSpace Ω] (Y : ℕ → Ω → ℕ) (hYm : ∀ j, Measurable (Y j)) (j : ℕ) :
    Measurable (wgt Y j) := by
  have hs : Measurable (fun ω => ∑ i ∈ range j, Y i ω) :=
    Finset.measurable_sum (range j) fun i _ => hYm i
  exact (measurable_from_nat (f := fun n : ℕ => (3⁻¹ : ℝ≥0∞) ^ n)).comp hs

/-- **Induction**: `E[W_k] ≤ (2/3)^k` under the integrated one-step bound for the history weights. -/
theorem weight_integral_le [MeasurableSpace Ω] (P : Measure Ω) (hP : P Set.univ = 1) (Y : ℕ → Ω → ℕ)
    (hYm : ∀ j, Measurable (Y j)) (hY : ∀ j ω, Y j ω ≤ 1)
    (hstep : ∀ j, 2⁻¹ * ∫⁻ ω, wgt Y j ω ∂P ≤ ∫⁻ ω, wgt Y j ω * (if Y j ω = 1 then 1 else 0) ∂P)
    (k : ℕ) : ∫⁻ ω, wgt Y k ω ∂P ≤ (2 * 3⁻¹) ^ k := by
  induction k with
  | zero =>
    simp [wgt, hP]
  | succ k ih =>
    have hfin : ∫⁻ ω, wgt Y k ω ∂P ≠ ⊤ := by
      refine ne_top_of_le_ne_top (ENNReal.one_ne_top) ?_
      calc ∫⁻ ω, wgt Y k ω ∂P ≤ ∫⁻ _ω, (1 : ℝ≥0∞) ∂P := lintegral_mono fun ω => wgt_le_one Y k ω
        _ = 1 := by simp [hP]
    have hone := one_step P (wgt_measurable Y hYm k) (hYm k) (hY k) hfin (hstep k)
    calc ∫⁻ ω, wgt Y (k + 1) ω ∂P = ∫⁻ ω, wgt Y k ω * (3⁻¹ : ℝ≥0∞) ^ Y k ω ∂P :=
          lintegral_congr fun ω => wgt_succ Y k ω
      _ ≤ (2 * 3⁻¹) * ∫⁻ ω, wgt Y k ω ∂P := hone
      _ ≤ (2 * 3⁻¹) * (2 * 3⁻¹) ^ k := mul_le_mul_of_nonneg_left ih (by positivity)
      _ = (2 * 3⁻¹) ^ (k + 1) := (pow_succ' _ _).symm

/-- `2 · 3⁻¹ = ofReal (2/3)` in `ℝ≥0∞`. -/
theorem two_mul_three_inv_eq_ofReal : (2 * 3⁻¹ : ℝ≥0∞) = ENNReal.ofReal (2 / 3) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  simp [div_eq_mul_inv]

/-- **Markov tail**: `P(4 ∑_{i<k} Y_i ≤ k) ≤ e^{-s₃ k}`, with `s₃ = ¾ log 3 − log 2`. -/
theorem absorbed_tail_le [MeasurableSpace Ω] (P : Measure Ω) (hP : P Set.univ = 1) (Y : ℕ → Ω → ℕ)
    (hYm : ∀ j, Measurable (Y j)) (hY : ∀ j ω, Y j ω ≤ 1)
    (hstep : ∀ j, 2⁻¹ * ∫⁻ ω, wgt Y j ω ∂P ≤ ∫⁻ ω, wgt Y j ω * (if Y j ω = 1 then 1 else 0) ∂P)
    (k : ℕ) :
    P {ω | 4 * (∑ i ∈ range k, Y i ω) ≤ k} ≤ ENNReal.ofReal (Real.exp (-s3 * k)) := by
  set S : Set Ω := {ω | 4 * (∑ i ∈ range k, Y i ω) ≤ k} with hSdef
  have hsum : Measurable (fun ω => ∑ i ∈ range k, Y i ω) :=
    Finset.measurable_sum (range k) fun i _ => hYm i
  have hSm : MeasurableSet S :=
    measurableSet_le (measurable_const.mul hsum) measurable_const
  set C : ℝ≥0∞ := ENNReal.ofReal ((3 : ℝ) ^ ((k : ℝ) / 4)) with hCdef
  have hpt : ∀ ω, S.indicator (1 : Ω → ℝ≥0∞) ω ≤ C * wgt Y k ω := by
    intro ω
    by_cases h : ω ∈ S
    · rw [Set.indicator_of_mem h]
      have hS : 4 * (∑ i ∈ range k, Y i ω) ≤ k := h
      have hNr : ((∑ i ∈ range k, Y i ω : ℕ) : ℝ) ≤ (k : ℝ) / 4 := by
        have : (4 : ℝ) * ((∑ i ∈ range k, Y i ω : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hS
        linarith
      have hpow : (3 : ℝ≥0∞) ^ (∑ i ∈ range k, Y i ω) ≤ C := by
        rw [hCdef, show (3 : ℝ≥0∞) ^ (∑ i ∈ range k, Y i ω) =
            ENNReal.ofReal ((3 : ℝ) ^ (∑ i ∈ range k, Y i ω)) by
          rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]]
        apply ENNReal.ofReal_le_ofReal
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hNr
      have h3 : (3 : ℝ≥0∞) * 3⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
      unfold wgt
      calc (1 : ℝ≥0∞) = (3 * 3⁻¹) ^ (∑ i ∈ range k, Y i ω) := by rw [h3, one_pow]
        _ = (3 : ℝ≥0∞) ^ (∑ i ∈ range k, Y i ω) * (3⁻¹ : ℝ≥0∞) ^ (∑ i ∈ range k, Y i ω) :=
            mul_pow _ _ _
        _ ≤ C * (3⁻¹ : ℝ≥0∞) ^ (∑ i ∈ range k, Y i ω) :=
            mul_le_mul_of_nonneg_right hpow (by positivity)
    · rw [Set.indicator_of_notMem h]
      exact zero_le
  calc P S = ∫⁻ ω, S.indicator (1 : Ω → ℝ≥0∞) ω ∂P := (lintegral_indicator_one hSm).symm
    _ ≤ ∫⁻ ω, C * wgt Y k ω ∂P := lintegral_mono hpt
    _ = C * ∫⁻ ω, wgt Y k ω ∂P := lintegral_const_mul _ (wgt_measurable Y hYm k)
    _ ≤ C * (2 * 3⁻¹) ^ k :=
        mul_le_mul_of_nonneg_left (weight_integral_le P hP Y hYm hY hstep k) (by positivity)
    _ = ENNReal.ofReal ((3 : ℝ) ^ ((k : ℝ) / 4) * ((2 : ℝ) / 3) ^ k) := by
        rw [hCdef, two_mul_three_inv_eq_ofReal, ← ENNReal.ofReal_pow (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (Real.exp (-s3 * k)) := by rw [rpow_mul_pow_eq_exp]

#print axioms MatedCRT.AbsorbedChernoff.weight_integral_le
#print axioms MatedCRT.AbsorbedChernoff.absorbed_tail_le

end AbsorbedChernoff

end MatedCRT
