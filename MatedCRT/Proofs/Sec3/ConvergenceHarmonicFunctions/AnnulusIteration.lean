import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnulusDisconnection

/-! # Iteration of annulus crossing estimates -/

namespace MatedCRT

open Set MeasureTheory
open scoped ENNReal

/-- The indicator for reaching the successive target sets before leaving the
corresponding regions. Stages are indexed in decreasing order, so the restart
vertex at stage `n + 1` belongs to the starting set of stage `n`. -/
noncomputable def annulusCrossings (A U B : ℕ → Set ℤ) : ℕ → (ℕ → ℤ) → ℝ≥0∞
  | 0, _ => 1
  | n + 1, x => ∑' k : ℕ,
      {x | vHitTime (A n ∪ (U n)ᶜ) x = k}.indicator
        (fun x => (B n).indicator 1 (x k) *
          annulusCrossings A U B n (pathShift k x)) x

/-- The finite-stage crossing indicator is measurable in the walk. -/
theorem measurable_annulusCrossings (A U B : ℕ → Set ℤ) (n : ℕ) :
    Measurable (annulusCrossings A U B n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    simp only [annulusCrossings]
    apply Measurable.tsum
    intro k
    exact (((measurable_of_countable ((B n).indicator (1 : ℤ → ℝ≥0∞))).comp
      (measurable_pi_apply k)).mul (ih.comp (measurable_pathShift k))).indicator
      (measurableSet_vHitTime_eq _ k)

/-- If each annulus crossing has probability at most `q`, the probability
of crossing all stages is at most the corresponding power of `q`. -/
theorem lintegral_annulusCrossings_le_pow
    (m : ℤ → ℤ → ℕ) (A U B S : ℕ → Set ℤ) (q : ℝ≥0∞)
    (hnext : ∀ n, B (n + 1) ⊆ S n)
    (hstage : ∀ n v, v ∈ S n →
      srwLaw m v (⋃ k : ℕ, {x | vHitTime (A n ∪ (U n)ᶜ) x = k ∧ x k ∈ B n}) ≤ q) :
    ∀ n v, v ∈ S n →
      (∫⁻ x, annulusCrossings A U B (n + 1) x ∂srwLaw m v) ≤ q ^ (n + 1) := by
  intro n
  induction n with
  | zero =>
    intro v hv
    simp only [annulusCrossings]
    rw [lintegral_tsum fun k => by
      exact ((((measurable_of_countable ((B 0).indicator (1 : ℤ → ℝ≥0∞))).comp
        (measurable_pi_apply k)).mul (measurable_const.comp (measurable_pathShift k))).indicator
        (measurableSet_vHitTime_eq _ k)).aemeasurable]
    calc
      _ ≤ srwLaw m v (⋃ k : ℕ, {x | vHitTime (A 0 ∪ (U 0)ᶜ) x = k ∧ x k ∈ B 0}) * 1 :=
        tsum_lintegral_hitTime_indicator_continuation_le_mul m _ (B 0) measurable_const v 1
          (fun b hb => by simp)
      _ ≤ q := by simpa using hstage 0 v hv
      _ = q ^ (0 + 1) := by simp
  | succ n ih =>
    intro v hv
    simp only [annulusCrossings]
    rw [lintegral_tsum fun k => by
      exact ((((measurable_of_countable ((B (n + 1)).indicator (1 : ℤ → ℝ≥0∞))).comp
        (measurable_pi_apply k)).mul ((measurable_annulusCrossings A U B (n + 1)).comp
          (measurable_pathShift k))).indicator (measurableSet_vHitTime_eq _ k)).aemeasurable]
    calc
      _ ≤ srwLaw m v (⋃ k : ℕ, {x | vHitTime (A (n + 1) ∪ (U (n + 1))ᶜ) x = k ∧
            x k ∈ B (n + 1)}) * q ^ (n + 1) :=
        tsum_lintegral_hitTime_indicator_continuation_le_mul m _ (B (n + 1))
          (measurable_annulusCrossings A U B (n + 1)) v (q ^ (n + 1))
          (fun b hb => ih b (hnext n hb))
      _ ≤ q * q ^ (n + 1) := by gcongr; exact hstage (n + 1) v hv
      _ = q ^ (n + 1 + 1) := by simp only [pow_succ]; ac_rfl

end MatedCRT
