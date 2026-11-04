import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.ModulusSubsequence

/-! Measurable selection of scales at which a property fails. -/

namespace MatedCRT

open Set MeasureTheory

/-- From a sequence of measurable events, choose measurably the first event at
or after a given index, using that index as a fallback if no event occurs. -/
theorem exists_measurable_bad_scale_selection
    {Ω : Type*} [MeasurableSpace Ω] (A : ℕ → Set Ω)
    (hA : ∀ n, MeasurableSet (A n)) :
    ∃ I : Ω → ℕ → ℕ, (∀ n, Measurable fun ω => I ω n) ∧
      (∀ ω n, n ≤ I ω n) ∧
      (∀ ω n, (∃ m, n ≤ m ∧ ω ∈ A m) → ω ∈ A (I ω n)) := by
  classical
  let P : ℕ → Ω → ℕ → Prop := fun n ω m => n ≤ m ∧
    (ω ∈ A m ∨ (m = n ∧ ¬ ∃ j, n ≤ j ∧ ω ∈ A j))
  have hex : ∀ n ω, ∃ m, P n ω m := by
    intro n ω
    by_cases h : ∃ j, n ≤ j ∧ ω ∈ A j
    · obtain ⟨j, hj, hAj⟩ := h
      exact ⟨j, hj, Or.inl hAj⟩
    · exact ⟨n, le_refl n, Or.inr ⟨rfl, h⟩⟩
  let I : Ω → ℕ → ℕ := fun ω n => Nat.find (hex n ω)
  refine ⟨I, ?_, ?_, ?_⟩
  · intro n
    apply measurable_find (hex n)
    intro m
    have hbad : MeasurableSet {ω | ∃ j, n ≤ j ∧ ω ∈ A j} := by
      have heq : {ω | ∃ j, n ≤ j ∧ ω ∈ A j} = ⋃ j, if n ≤ j then A j else ∅ := by
        ext ω
        simp only [mem_ofPred_eq, mem_iUnion]
        constructor
        · rintro ⟨j, hj, hAj⟩
          exact ⟨j, by simpa [hj] using hAj⟩
        · rintro ⟨j, hj⟩
          by_cases h : n ≤ j
          · exact ⟨j, h, by simpa [h] using hj⟩
          · simp [h] at hj
      rw [heq]
      apply MeasurableSet.iUnion
      intro j
      split_ifs
      · exact hA j
      · exact MeasurableSet.empty
    have heq : {ω | P n ω m} = if n ≤ m then
        (A m ∪ if m = n then {ω | ¬ ∃ j, n ≤ j ∧ ω ∈ A j} else ∅) else ∅ := by
      ext ω
      simp only [P, mem_ofPred_eq]
      split_ifs <;> simp_all
    rw [heq]
    split_ifs
    · exact (hA m).union hbad.compl
    · exact (hA m).union MeasurableSet.empty
    · exact MeasurableSet.empty
  · intro ω n
    exact (Nat.find_spec (hex n ω)).1
  · intro ω n h
    rcases (Nat.find_spec (hex n ω)).2 with hmem | ⟨_, hnone⟩
    · exact hmem
    · exact False.elim (hnone h)

end MatedCRT
