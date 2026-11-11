import MatedCRT.Defs.RandomWalk

/-!
# Monotonicity of stopped IDLA in the stopping domain

Used in the stopped clause of Proposition 5.1:
for stopping domains `Θ₁ ⊆ Θ₂`, every site occupied by IDLA stopped upon leaving `Θ₁` is occupied by IDLA stopped upon
leaving `Θ₂`, for the same walker paths. The argument is deterministic: induction on the walkers, with the invariant
`A₁ ⊆ A₂` on the two aggregates.
-/

namespace MatedCRT

open Classical

/-- A walker that first leaves `A₁` at a site outside `A₂ ⊇ A₁` also first leaves `A₂` there. -/
theorem stoppedFirstExitSite_eq_of_subset {A₁ A₂ : Set ℤ} (hA : A₁ ⊆ A₂) {x : ℕ → ℤ} {b : ℤ}
    (h₁ : firstExitSite A₁ x = some b) (hb : b ∉ A₂) : firstExitSite A₂ x = some b := by
  unfold firstExitSite at h₁ ⊢
  split_ifs at h₁ with hex₁
  · obtain rfl := Option.some_injective _ h₁
    have hτ₁ : ∃ n, x n ∉ A₂ := ⟨Nat.find hex₁, hb⟩
    have hle : Nat.find hτ₁ ≤ Nat.find hex₁ := Nat.find_min' hτ₁ hb
    have heq : Nat.find hτ₁ = Nat.find hex₁ := by
      by_contra hne
      have hlt : Nat.find hτ₁ < Nat.find hex₁ := lt_of_le_of_ne hle hne
      have hmem : x (Nat.find hτ₁) ∈ A₁ := by
        by_contra hnot
        exact Nat.find_min hex₁ hlt hnot
      exact (Nat.find_spec hτ₁) (hA hmem)
    simp only [hτ₁, dite_true, heq]

/-- A step of the stopped IDLA process never removes sites from the aggregate. -/
theorem subset_idlaStep_fst (Θ' : Set ℤ) (s : Set ℤ × List ℤ) (x : ℕ → ℤ) :
    s.1 ⊆ (idlaStep Θ' s x).1 := by
  cases h : firstExitSite s.1 x with
  | none => simp [idlaStep, h]
  | some b =>
    by_cases hb : b ∈ Θ'
    · simp [idlaStep, h, hb]
    · simp [idlaStep, h, hb]

/-- One walker preserves the inclusion of the aggregates, for ordered stopping domains. -/
theorem idlaStep_fst_mono {Θ₁ Θ₂ : Set ℤ} (hΘ : Θ₁ ⊆ Θ₂) {s₁ s₂ : Set ℤ × List ℤ} (hs : s₁.1 ⊆ s₂.1)
    (x : ℕ → ℤ) : (idlaStep Θ₁ s₁ x).1 ⊆ (idlaStep Θ₂ s₂ x).1 := by
  have hA := subset_idlaStep_fst Θ₂ s₂ x
  cases h₁ : firstExitSite s₁.1 x with
  | none =>
    have e₁ : idlaStep Θ₁ s₁ x = s₁ := by simp [idlaStep, h₁]
    rw [e₁]
    exact hs.trans hA
  | some b₁ =>
    by_cases hb₁ : b₁ ∈ Θ₁
    · have e₁ : idlaStep Θ₁ s₁ x = (s₁.1 ∪ {b₁}, s₁.2) := by simp [idlaStep, h₁, hb₁]
      rw [e₁]
      by_cases hb₂ : b₁ ∈ s₂.1
      · exact Set.union_subset (hs.trans hA) (Set.singleton_subset_iff.mpr (hA hb₂))
      · have h₂ := stoppedFirstExitSite_eq_of_subset hs h₁ hb₂
        have e₂ : idlaStep Θ₂ s₂ x = (s₂.1 ∪ {b₁}, s₂.2) := by
          simp [idlaStep, h₂, hΘ hb₁]
        rw [e₂]
        exact Set.union_subset (hs.trans Set.subset_union_left)
          (Set.singleton_subset_iff.mpr (Set.mem_union_right _ rfl))
    · have e₁ : idlaStep Θ₁ s₁ x = (s₁.1, s₁.2 ++ [b₁]) := by simp [idlaStep, h₁, hb₁]
      rw [e₁]
      exact hs.trans hA

/-- Several walkers: the aggregates stay ordered when the stopping domains are ordered. -/
theorem idlaRun_fst_mono {Θ₁ Θ₂ : Set ℤ} (hΘ : Θ₁ ⊆ Θ₂) (xs : List (ℕ → ℤ)) :
    ∀ s₁ s₂ : Set ℤ × List ℤ, s₁.1 ⊆ s₂.1 →
      (xs.foldl (idlaStep Θ₁) s₁).1 ⊆ (xs.foldl (idlaStep Θ₂) s₂).1 := by
  induction xs with
  | nil => intro s₁ s₂ hs; exact hs
  | cons x xs ih =>
    intro s₁ s₂ hs
    exact ih _ _ (idlaStep_fst_mono hΘ hs x)

/-- **Monotonicity of stopped IDLA.** For `Θ₁ ⊆ Θ₂`, the IDLA cluster after `n` walkers stopped upon leaving `Θ₁` is
contained in the one stopped upon leaving `Θ₂`, for the same walker paths. -/
theorem stoppedIDLACluster_mono_domain {Θ₁ Θ₂ : Set ℤ} (hΘ : Θ₁ ⊆ Θ₂) (xs : ℕ → ℕ → ℤ) (n : ℕ) :
    stoppedIDLACluster Θ₁ xs n ⊆ stoppedIDLACluster Θ₂ xs n :=
  idlaRun_fst_mono hΘ _ _ _ subset_rfl

end MatedCRT
