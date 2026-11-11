import MatedCRT.FirstPass.S4S6c.Lemma3Green

/-!
# Lemma 3: the counting bound and the first moment

* `counting_half`: if the vertices of `D₀` number at least `ε⁻¹ (m₀ − e₁)` (the counting bound of Lemma 2.9 at `f ≡ 1`, eq (16)),
  and the sparse set `A` meets them in at most `ε⁻¹ s` vertices (the sparsity hypothesis `|A ∩ V(B_r)| < s₁ r^{2β⁻} ε⁻¹`, with
  `s = ¼ r^{2β⁻}`), with `e₁ ≤ m₀/4` and `s ≤ m₀/4`, then `|V(D₀) \ A| ≥ ½ ε⁻¹ m₀` (eq (18)).
* `first_moment_ge`: with the Green identity bound `|B| · ½ ≤ E[V]` of `Lemma3Green.green_occupation_ge` (eq (20)), this gives
  `E[V] ≥ ¼ ε⁻¹ m₀`, the first-moment hypothesis `hE1` of `Lemma3Second.eq15_of_moments`.
-/

open MeasureTheory
open scoped ENNReal

namespace MatedCRT

namespace Lemma3Counting

/-- **eq (18)**: the counting bound minus the sparse set. -/
theorem counting_half {α : Type*} [DecidableEq α] (S T : Finset α) {ε m0 e1 s : ℝ}
    (hε : 0 < ε) (he1 : e1 ≤ m0 / 4) (hs : s ≤ m0 / 4)
    (hS : ε⁻¹ * (m0 - e1) ≤ (S.card : ℝ)) (hT : (T.card : ℝ) ≤ ε⁻¹ * s) :
    ε⁻¹ * (m0 / 2) ≤ ((S \ T).card : ℝ) := by
  have hinv : 0 < ε⁻¹ := inv_pos.2 hε
  have hc : ((S \ T).card : ℝ) + ((S ∩ T).card : ℝ) = (S.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_inter S T
  have hi : ((S ∩ T).card : ℝ) ≤ (T.card : ℝ) := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  have key : ε⁻¹ * (m0 / 2) ≤ ε⁻¹ * (m0 - e1) - ε⁻¹ * s := by
    rw [← mul_sub]
    exact mul_le_mul_of_nonneg_left (by linarith) hinv.le
  linarith

/-- **First moment** (eqs (16)-(20)): the Green identity bound and the counting bound give `E[V] ≥ ¼ ε⁻¹ m₀`. -/
theorem first_moment_ge {α : Type*} [DecidableEq α] (S T : Finset α) {ε m0 e1 s : ℝ}
    (hε : 0 < ε) (hm0 : 0 < m0) (he1 : e1 ≤ m0 / 4) (hs : s ≤ m0 / 4)
    (hS : ε⁻¹ * (m0 - e1) ≤ (S.card : ℝ)) (hT : (T.card : ℝ) ≤ ε⁻¹ * s)
    {EV : ℝ≥0∞} (hEV : (((S \ T).card : ℕ) : ℝ≥0∞) * (1 / 2) ≤ EV) :
    ENNReal.ofReal ((1 / 4) * ε⁻¹ * m0) ≤ EV := by
  have hcardR := counting_half S T hε he1 hs hS hT
  have hc2 : ENNReal.ofReal (ε⁻¹ * (m0 / 2)) ≤ ((S \ T).card : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hcardR
  calc ENNReal.ofReal ((1 / 4) * ε⁻¹ * m0)
      = ENNReal.ofReal (ε⁻¹ * (m0 / 2)) * ENNReal.ofReal (1 / 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
    _ ≤ ((S \ T).card : ℝ≥0∞) * ENNReal.ofReal (1 / 2) :=
        mul_le_mul_of_nonneg_right hc2 (by positivity)
    _ = ((S \ T).card : ℝ≥0∞) * (1 / 2) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num
    _ ≤ EV := hEV

#print axioms MatedCRT.Lemma3Counting.counting_half
#print axioms MatedCRT.Lemma3Counting.first_moment_ge

end Lemma3Counting

end MatedCRT
