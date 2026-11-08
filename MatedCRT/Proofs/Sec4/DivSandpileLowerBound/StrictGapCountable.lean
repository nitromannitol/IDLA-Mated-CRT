import Mathlib.Topology.Bases
import Mathlib.Data.Real.Basic

/-! First appearances in a family of open sets. -/

namespace MatedCRT

open Set

/-- In a second-countable space, a family of open sets has only
countably many times at which a point appears for the first time. -/
theorem countable_firstAppearance {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] (O : ℝ → Set X)
    (hopen : ∀ t, IsOpen (O t)) :
    {t : ℝ | ∃ x ∈ O t, ∀ s < t, x ∉ O s}.Countable := by
  classical
  let E : Set ℝ := {t | ∃ x ∈ O t, ∀ s < t, x ∉ O s}
  have hw : ∀ t : E, ∃ B ∈ TopologicalSpace.countableBasis X,
      B ⊆ O t.1 ∧ ∀ s < t.1, ¬ B ⊆ O s := by
    intro t
    obtain ⟨x, hx, hxearlier⟩ := t.2
    obtain ⟨B, hB, hxB, hBO⟩ :=
      (TopologicalSpace.isBasis_countableBasis X).exists_subset_of_mem_open hx (hopen t.1)
    exact ⟨B, hB, hBO, fun s hs hsub => hxearlier s hs (hsub hxB)⟩
  let B : E → TopologicalSpace.countableBasis X :=
    fun t => ⟨Classical.choose (hw t), (Classical.choose_spec (hw t)).1⟩
  have hB (t : E) : (B t : Set X) ⊆ O t.1 ∧
      ∀ s < t.1, ¬ (B t : Set X) ⊆ O s :=
    (Classical.choose_spec (hw t)).2
  have hinj : Function.Injective B := by
    intro a b hab
    apply Subtype.ext
    rcases lt_trichotomy a.1 b.1 with hab' | hab' | hab'
    · exfalso
      apply (hB b).2 a.1 hab'
      rw [← congrArg Subtype.val hab]
      exact (hB a).1
    · exact hab'
    · exfalso
      apply (hB a).2 b.1 hab'
      rw [congrArg Subtype.val hab]
      exact (hB b).1
  exact Set.countable_coe_iff.mp hinj.countable

/-- A comparison of earlier regularized sets with the current raw set
makes the positive-time regularization defects countable. The predicate `good`
can encode compact containment of the current raw cluster. -/
theorem countable_regularization_defects {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] (C A : ℝ → Set X) (good : ℝ → Prop)
    (hopen : ∀ t, 0 < t → IsOpen (A t))
    (hsubset : ∀ t, 0 < t → C t ⊆ A t)
    (hcompare : ∀ s t, 0 < s → s < t → good t → A s ⊆ C t) :
    {t : ℝ | 0 < t ∧ good t ∧ A t ≠ C t}.Countable := by
  classical
  let O : ℝ → Set X := fun t => if 0 < t then A t else ∅
  have hO : ∀ t, IsOpen (O t) := by
    intro t
    by_cases ht : 0 < t
    · simpa [O, ht] using hopen t ht
    · simp [O, ht]
  apply (countable_firstAppearance O hO).mono
  intro t ht
  have hnot : ¬ A t ⊆ C t := by
    intro h
    exact ht.2.2 (Set.Subset.antisymm h (hsubset t ht.1))
  obtain ⟨x, hxA, hxC⟩ := Set.not_subset.mp hnot
  refine ⟨x, by simpa [O, ht.1] using hxA, ?_⟩
  intro s hst
  by_cases hs : 0 < s
  · simpa [O, hs] using fun hx => hxC (hcompare s t hs hst ht.2.1 hx)
  · simp [O, hs]

/-- Applied to raw open clusters, the comparison of earlier regularizations
with the current cluster gives countability of compactly confined defects. -/
theorem countable_open_cluster_regularization_defects
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    (C : ℝ → Set X) (good : ℝ → Prop)
    (hopen : ∀ t, 0 < t → IsOpen (C t))
    (hcompare : ∀ s t, 0 < s → s < t → good t →
      interior (closure (C s)) ⊆ C t) :
    {t : ℝ | 0 < t ∧ good t ∧ interior (closure (C t)) ≠ C t}.Countable :=
  countable_regularization_defects C (fun t => interior (closure (C t))) good
    (fun _ _ => isOpen_interior) (fun t ht => (hopen t ht).subset_interior_closure) hcompare

end MatedCRT
