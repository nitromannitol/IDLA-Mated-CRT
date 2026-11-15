import MatedCRT.Defs.Map

/-! # Side-count conventions and Brownian edge multiplicity -/

set_option autoImplicit false

namespace MatedCRT

open Set

/-- Conditional on the two side predicates matching the contour criteria, the
consecutive-suppressed sided count is the Brownian edge multiplicity. -/
theorem bmEdgeCount_eq_sided_count
    {Ω : Type*} (A B : Ω → Prop) (ω : Ω) (ε : ℝ) (L R : ℝ → ℝ) (j k : ℤ)
    (hA : A ω ↔ bmAdjacent ε L (min j k) (max j k))
    (hB : B ω ↔ bmAdjacent ε R (min j k) (max j k)) :
    bmEdgeCount ε L R j k =
      ({ω | j ≠ k ∧ (A ω ∨ B ω)}.indicator (fun _ => (1 : ℕ))) ω +
      ({ω | j ≠ k ∧ A ω ∧ B ω ∧ 1 < max j k - min j k}.indicator
        (fun _ => (1 : ℕ))) ω := by
  classical
  simp only [bmEdgeCount, ← hA, ← hB]
  by_cases hj : j = k <;> by_cases ha : A ω <;> by_cases hb : B ω <;>
    by_cases hg : 1 < max j k - min j k <;>
    simp [Set.indicator, hj, ha, hb, hg]

/-- Counting both side predicates also on consecutive pairs adds the indicator
of the distinct, consecutive, two-sided event to the Brownian edge multiplicity. -/
theorem sided_count_eq_bmEdgeCount_add
    {Ω : Type*} (A B : Ω → Prop) (ω : Ω) (ε : ℝ) (L R : ℝ → ℝ) (j k : ℤ)
    (hA : A ω ↔ bmAdjacent ε L (min j k) (max j k))
    (hB : B ω ↔ bmAdjacent ε R (min j k) (max j k)) :
    ({ω | j ≠ k ∧ (A ω ∨ B ω)}.indicator (fun _ => (1 : ℕ))) ω +
      ({ω | j ≠ k ∧ A ω ∧ B ω}.indicator (fun _ => (1 : ℕ))) ω =
      bmEdgeCount ε L R j k +
      ({ω | j ≠ k ∧ A ω ∧ B ω ∧ ¬ 1 < max j k - min j k}.indicator
        (fun _ => (1 : ℕ))) ω := by
  classical
  simp only [bmEdgeCount, ← hA, ← hB]
  by_cases hj : j = k <;> by_cases ha : A ω <;> by_cases hb : B ω <;>
    by_cases hg : 1 < max j k - min j k <;>
    simp [Set.indicator, hj, ha, hb, hg]

end MatedCRT
