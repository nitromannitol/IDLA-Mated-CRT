import MatedCRT.FirstPass.Derived.BoundaryLengthProtectedMeasurable

/-!
# Measurability of the past boundary criterion

The past-edge and protected-minimum alternatives are measurable when the
interval endpoints are measurable from the observed path.
-/

set_option autoImplicit false

open Set MeasureTheory

namespace MatedCRT

/-- The past-edge and protected-minimum alternatives are measurable for
measurable interval endpoints and a fixed mesh. -/
theorem measurableSet_pastBoundaryCandidate {Ω : Type} [MeasurableSpace Ω]
    (B : Ω → C(ℝ, ℝ × ℝ)) (s ε : ℝ)
    (hB : ∀ t ≤ s, Measurable fun ω => B ω t)
    (hε : 0 ≤ ε) (j n : ℤ) (hjn : j ≤ n) (hn : ε * n ≤ s)
    (α β : Ω → ℝ) (hα : Measurable α) (hβ : Measurable β) :
    MeasurableSet {ω |
      (∃ k : ℤ, k ≤ n ∧ ¬ (α ω ≤ ε * k ∧ ε * k ≤ β ω) ∧
        bmEdgeCount ε (fun t => (B ω t).1) (fun t => (B ω t).2) j k ≠ 0) ∨
      (∀ u ∈ Icc (ε * j) (ε * n),
        sInf ((fun t => (B ω t).1) '' Icc (ε * j - ε) (ε * j)) ≤ (B ω u).1) ∨
      (∀ u ∈ Icc (ε * j) (ε * n),
        sInf ((fun t => (B ω t).2) '' Icc (ε * j - ε) (ε * j)) ≤ (B ω u).2)} := by
  have hedge : MeasurableSet {ω | ∃ k : ℤ, k ≤ n ∧
      ¬ (α ω ≤ ε * k ∧ ε * k ≤ β ω) ∧
      bmEdgeCount ε (fun t => (B ω t).1) (fun t => (B ω t).2) j k ≠ 0} := by
    simp only [show {ω | ∃ k : ℤ, k ≤ n ∧
      ¬ (α ω ≤ ε * k ∧ ε * k ≤ β ω) ∧
      bmEdgeCount ε (fun t => (B ω t).1) (fun t => (B ω t).2) j k ≠ 0} =
      ⋃ k : ℤ, {ω | k ≤ n ∧ ¬ (α ω ≤ ε * k ∧ ε * k ≤ β ω) ∧
        bmEdgeCount ε (fun t => (B ω t).1) (fun t => (B ω t).2) j k ≠ 0} by
          ext ω; simp only [mem_ofPred_eq, mem_iUnion]]
    apply MeasurableSet.iUnion
    intro k
    by_cases hk : k ≤ n
    · have hmax : ε * ((max j k : ℤ) : ℝ) ≤ s := by
        have hcast : ((max j k : ℤ) : ℝ) ≤ n := by
          exact_mod_cast (max_le hjn hk)
        exact (mul_le_mul_of_nonneg_left hcast hε).trans hn
      have he := measurable_bmEdgeCount_of_past B s ε hB hε j k hmax
      have hout : MeasurableSet {ω | ¬ (α ω ≤ ε * k ∧ ε * k ≤ β ω)} :=
        ((measurableSet_le hα measurable_const).inter
          (measurableSet_le measurable_const hβ)).compl
      simpa [hk, Set.inter_def] using hout.inter ((measurableSet_eq_fun he measurable_const).compl)
    · simpa only [hk, false_and, ofPred_false] using (MeasurableSet.empty : MeasurableSet (∅ : Set Ω))
  have hleft := measurableSet_cellMin_protected_of_past B s ε hB hε j n hjn hn
    Prod.fst continuous_fst
  have hright := measurableSet_cellMin_protected_of_past B s ε hB hε j n hjn hn
    Prod.snd continuous_snd
  exact hedge.union (hleft.union hright)

end MatedCRT
