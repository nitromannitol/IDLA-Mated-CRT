import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Visit

/-!
# Lemma 3: the expected occupation from the Green lower bound

For a path measure `μ` on `ℕ → ℤ` and a finite set `B` of vertices, the expected number of visits to `B` before the exit
time `τ_A = vExitTime A` is `∑_{b∈B} G(b)`, with the discrete Green function `G(b) = ∑_n μ{n < τ_A, x_n = b}`. The Green lower
bound `G(b) ≥ ½` on `B` (Lemma 2.16; Draft Section2:207; in the walk model) then gives `E[V] ≥ |B|/2`, where
`V = ∑_{n < τ_A} 1{x_n ∈ B}` is the occupation count. The counting bound `|B| ≥ ¼ ε⁻¹ m₀` and the Lemma 2.16
inequality are the inputs of eq (20).
-/

open MeasureTheory
open scoped ENNReal

namespace MatedCRT

namespace Lemma3Green

/-- **Expected occupation from the Green lower bound** (eq (20) in the walk model). -/
theorem green_occupation_ge (μ : Measure (ℕ → ℤ)) (A : Set ℤ) (B : Finset ℤ)
    (hG : ∀ b ∈ B, (1 / 2 : ℝ≥0∞) ≤ ∑' n : ℕ, μ {x | (n : ℕ∞) < vExitTime A x ∧ x n = b}) :
    (B.card : ℝ≥0∞) * (1 / 2) ≤
      ∫⁻ x, ∑' n : ℕ, (if (n : ℕ∞) < vExitTime A x ∧ x n ∈ B then (1 : ℝ≥0∞) else 0) ∂μ := by
  have hsplit : ∀ (x : ℕ → ℤ) (n : ℕ),
      (if (n : ℕ∞) < vExitTime A x ∧ x n ∈ B then (1 : ℝ≥0∞) else 0) =
        ∑ b ∈ B, (if (n : ℕ∞) < vExitTime A x ∧ x n = b then (1 : ℝ≥0∞) else 0) := by
    intro x n
    by_cases hp : (n : ℕ∞) < vExitTime A x
    · simp [hp, Finset.sum_ite_eq]
    · simp [hp]
  have hind : ∀ (n : ℕ) (b : ℤ),
      (fun x : ℕ → ℤ => (if (n : ℕ∞) < vExitTime A x ∧ x n = b then (1 : ℝ≥0∞) else 0)) =
        {x : ℕ → ℤ | (n : ℕ∞) < vExitTime A x ∧ x n = b}.indicator 1 := by
    intro n b
    funext x
    by_cases h : (n : ℕ∞) < vExitTime A x ∧ x n = b
    · simp [h]
    · simp [h]
  have hmeas : ∀ (n : ℕ) (b : ℤ),
      MeasurableSet {x : ℕ → ℤ | (n : ℕ∞) < vExitTime A x ∧ x n = b} :=
    fun n b => (ConstantOrderDiv.measurableSet_lt_vExitTime A n).inter
      (measurableSet_eq_fun (measurable_pi_apply n) measurable_const)
  calc (B.card : ℝ≥0∞) * (1 / 2) = ∑ b ∈ B, (1 / 2 : ℝ≥0∞) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ b ∈ B, ∑' n : ℕ, μ {x | (n : ℕ∞) < vExitTime A x ∧ x n = b} :=
        Finset.sum_le_sum fun b hb => hG b hb
    _ = ∑' n : ℕ, ∑ b ∈ B, μ {x | (n : ℕ∞) < vExitTime A x ∧ x n = b} :=
        (Summable.tsum_finsetSum fun b _ => ENNReal.summable).symm
    _ = ∑' n : ℕ, ∫⁻ x, ∑ b ∈ B, {x : ℕ → ℤ | (n : ℕ∞) < vExitTime A x ∧ x n = b}.indicator 1 x ∂μ := by
        refine tsum_congr fun n => ?_
        rw [lintegral_finsetSum B (fun b _ => measurable_one.indicator (hmeas n b))]
        exact Finset.sum_congr rfl fun b _ => (lintegral_indicator_one (hmeas n b)).symm
    _ = ∫⁻ x, ∑' n : ℕ, ∑ b ∈ B, {x : ℕ → ℤ | (n : ℕ∞) < vExitTime A x ∧ x n = b}.indicator 1 x ∂μ :=
        (lintegral_tsum fun n =>
          (Finset.measurable_sum B fun b _ => measurable_one.indicator (hmeas n b)).aemeasurable).symm
    _ = ∫⁻ x, ∑' n : ℕ, (if (n : ℕ∞) < vExitTime A x ∧ x n ∈ B then (1 : ℝ≥0∞) else 0) ∂μ := by
        refine lintegral_congr fun x => tsum_congr fun n => ?_
        rw [hsplit x n]
        exact Finset.sum_congr rfl fun b _ => (congrFun (hind n b) x).symm

#print axioms MatedCRT.Lemma3Green.green_occupation_ge

end Lemma3Green

end MatedCRT
