import MatedCRT.Proofs.IDLA.Basic

/-!
# IDLA on a fixed multigraph: monotonicity in the occupied set, and the stopped run from the empty set

* `idlaAggregate_univ_mono`: **IDLA is monotone in the initially occupied set**, path by path: for the same walker
  paths, `A ⊆ A'` implies `A(A; x₁, …, x_k) ⊆ A(A'; x₁, …, x_k)`. A walker leaves the larger aggregate at the site where
  it leaves the smaller one, unless that site is already occupied in the larger one.
* `foldl_idlaStep_card`: each walker adds at most one site to the aggregate or one stopped position, so
  `|A(∅; x → Θ')| + |P(∅; x → Θ')| ≤ k` (Definition 6.2).
* `foldl_idlaStep_subset`: the stopped run absorbs only inside `Θ'`.
* `foldl_idlaStep_stopped_adj`: if the walkers start at a site `z ∈ Θ'` and move along edges, every stopped position is
  joined by an edge to the aggregate.
-/

namespace MatedCRT

open Set

/-! ### The first exit site -/

open Classical in
/-- The first exit site `b` of a path from `A` is visited at some time `N`, before which the path stays in `A`. -/
theorem exists_of_firstExitSite_eq_some {A : Set ℤ} {x : ℕ → ℤ} {b : ℤ} (hb : firstExitSite A x = some b) :
    ∃ N, x N = b ∧ b ∉ A ∧ ∀ j < N, x j ∈ A := by
  unfold firstExitSite at hb
  by_cases h : ∃ n, x n ∉ A
  · rw [dite_eq_left h] at hb
    have hb' : x (Nat.find h) = b := Option.some.inj hb
    exact ⟨Nat.find h, hb', hb' ▸ Nat.find_spec h, fun j hj => not_not.1 (Nat.find_min h hj)⟩
  · simp [h] at hb

open Classical in
/-- A path which is outside `A` at time `N` and in `A` before leaves `A` at `x N`. -/
theorem firstExitSite_eq_some_of {A : Set ℤ} {x : ℕ → ℤ} {N : ℕ} (hN : x N ∉ A) (hlt : ∀ j < N, x j ∈ A) :
    firstExitSite A x = some (x N) := by
  have h : ∃ n, x n ∉ A := ⟨N, hN⟩
  unfold firstExitSite
  rw [dite_eq_left h]
  have hfind : Nat.find h = N :=
    le_antisymm (Nat.find_min' h hN) (not_lt.1 fun hlt' => Nat.find_spec h (hlt _ hlt'))
  rw [hfind]

/-- If the first exit site `b` of a path from `A` lies outside `A' ⊇ A`, it is its first exit site from `A'`. -/
theorem firstExitSite_eq_of_subset {A A' : Set ℤ} (hA : A ⊆ A') {x : ℕ → ℤ} {b : ℤ}
    (hb : firstExitSite A x = some b) (hbA' : b ∉ A') : firstExitSite A' x = some b := by
  obtain ⟨N, hN, _, hlt⟩ := exists_of_firstExitSite_eq_some hb
  rw [← hN] at hbA' ⊢
  exact firstExitSite_eq_some_of hbA' fun j hj => hA (hlt j hj)

/-! ### One walker -/

theorem idlaStep_of_none {Θ' : Set ℤ} {s : Set ℤ × List ℤ} {x : ℕ → ℤ} (h : firstExitSite s.1 x = none) :
    idlaStep Θ' s x = s := by
  simp [idlaStep, h]

theorem idlaStep_of_some_mem {Θ' : Set ℤ} {s : Set ℤ × List ℤ} {x : ℕ → ℤ} {b : ℤ}
    (h : firstExitSite s.1 x = some b) (hb : b ∈ Θ') : idlaStep Θ' s x = (s.1 ∪ {b}, s.2) := by
  simp [idlaStep, h, hb]

theorem idlaStep_of_some_not_mem {Θ' : Set ℤ} {s : Set ℤ × List ℤ} {x : ℕ → ℤ} {b : ℤ}
    (h : firstExitSite s.1 x = some b) (hb : b ∉ Θ') : idlaStep Θ' s x = (s.1, s.2 ++ [b]) := by
  simp [idlaStep, h, hb]

/-- One walker without stopping: the aggregate is monotone in the occupied set. -/
theorem idlaStep_univ_fst_mono {s s' : Set ℤ × List ℤ} (h : s.1 ⊆ s'.1) (x : ℕ → ℤ) :
    (idlaStep univ s x).1 ⊆ (idlaStep univ s' x).1 := by
  have hs' : s'.1 ⊆ (idlaStep univ s' x).1 := idlaStep_fst_subset univ s' x
  cases hb : firstExitSite s.1 x with
  | none =>
    rw [idlaStep_of_none hb]
    exact h.trans hs'
  | some b =>
    rw [idlaStep_of_some_mem hb (mem_univ b)]
    by_cases hbA' : b ∈ s'.1
    · exact union_subset (h.trans hs') (singleton_subset_iff.2 (hs' hbA'))
    · rw [idlaStep_of_some_mem (firstExitSite_eq_of_subset h hb hbA') (mem_univ b)]
      exact union_subset_union_left _ h

/-- Without stopping, the aggregate is monotone in the occupied set, path by path. -/
theorem foldl_idlaStep_univ_fst_mono :
    ∀ (xs : List (ℕ → ℤ)) {s s' : Set ℤ × List ℤ}, s.1 ⊆ s'.1 →
      (xs.foldl (idlaStep univ) s).1 ⊆ (xs.foldl (idlaStep univ) s').1
  | [], _, _, h => h
  | x :: xs, _, _, h => by
    rw [List.foldl_cons, List.foldl_cons]
    exact foldl_idlaStep_univ_fst_mono xs (idlaStep_univ_fst_mono h x)

/-- **IDLA is monotone in the initially occupied set**, path by path: `A ⊆ A'` implies
`A(A; x₁, …, x_k) ⊆ A(A'; x₁, …, x_k)`. -/
theorem idlaAggregate_univ_mono {A A' : Set ℤ} (h : A ⊆ A') (xs : List (ℕ → ℤ)) :
    idlaAggregate A univ xs ⊆ idlaAggregate A' univ xs :=
  foldl_idlaStep_univ_fst_mono xs (s := (A, [])) (s' := (A', [])) h

/-! ### The stopped run -/

/-- One walker adds at most one site to the aggregate or one stopped position. -/
theorem idlaStep_card (Θ' : Set ℤ) (s : Set ℤ × List ℤ) (x : ℕ → ℤ) (hs : s.1.Finite) :
    (idlaStep Θ' s x).1.Finite ∧
      (idlaStep Θ' s x).1.ncard + (idlaStep Θ' s x).2.length ≤ s.1.ncard + s.2.length + 1 := by
  cases h : firstExitSite s.1 x with
  | none =>
    rw [idlaStep_of_none h]
    exact ⟨hs, by omega⟩
  | some b =>
    by_cases hb : b ∈ Θ'
    · rw [idlaStep_of_some_mem h hb]
      refine ⟨hs.union (finite_singleton b), ?_⟩
      have hle := ncard_union_le s.1 {b}
      rw [ncard_singleton] at hle
      dsimp only
      omega
    · rw [idlaStep_of_some_not_mem h hb]
      refine ⟨hs, ?_⟩
      simp only [List.length_append, List.length_singleton]
      omega

/-- `|A(s; x → Θ')| + |P(s; x → Θ')| ≤ |s.1| + |s.2| + k`. -/
theorem foldl_idlaStep_card (Θ' : Set ℤ) :
    ∀ (xs : List (ℕ → ℤ)) (s : Set ℤ × List ℤ), s.1.Finite →
      (xs.foldl (idlaStep Θ') s).1.Finite ∧
        (xs.foldl (idlaStep Θ') s).1.ncard + (xs.foldl (idlaStep Θ') s).2.length ≤
          s.1.ncard + s.2.length + xs.length
  | [], s, hs => ⟨hs, by simp⟩
  | x :: xs, s, hs => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := idlaStep_card Θ' s x hs
    obtain ⟨h3, h4⟩ := foldl_idlaStep_card Θ' xs _ h1
    refine ⟨h3, h4.trans ?_⟩
    simp only [List.length_cons]
    omega

/-- One walker absorbs only inside `Θ'`. -/
theorem idlaStep_fst_subset_union (Θ' : Set ℤ) (s : Set ℤ × List ℤ) (x : ℕ → ℤ) :
    (idlaStep Θ' s x).1 ⊆ s.1 ∪ Θ' := by
  cases h : firstExitSite s.1 x with
  | none =>
    rw [idlaStep_of_none h]
    exact subset_union_left
  | some b =>
    by_cases hb : b ∈ Θ'
    · rw [idlaStep_of_some_mem h hb]
      exact union_subset_union_right _ (singleton_subset_iff.2 hb)
    · rw [idlaStep_of_some_not_mem h hb]
      exact subset_union_left

/-- The stopped run absorbs only inside `Θ'`. -/
theorem foldl_idlaStep_subset (Θ' : Set ℤ) :
    ∀ (xs : List (ℕ → ℤ)) (s : Set ℤ × List ℤ), (xs.foldl (idlaStep Θ') s).1 ⊆ s.1 ∪ Θ'
  | [], s => subset_union_left
  | x :: xs, s => by
    rw [List.foldl_cons]
    refine (foldl_idlaStep_subset Θ' xs _).trans ?_
    exact union_subset (idlaStep_fst_subset_union Θ' s x) subset_union_right

/-- One walker started in `s.1 ∪ Θ'` and moving along edges: a stopped position is joined by an edge to the
aggregate. -/
theorem idlaStep_stopped_adj (m : ℤ → ℤ → ℕ) {Θ' : Set ℤ} {s : Set ℤ × List ℤ} {x : ℕ → ℤ}
    (hx0 : x 0 ∈ s.1 ∪ Θ') (hx : ∀ n, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0)
    (hs : ∀ b ∈ s.2, ∃ a ∈ s.1, m a b ≠ 0) :
    ∀ b ∈ (idlaStep Θ' s x).2, ∃ a ∈ (idlaStep Θ' s x).1, m a b ≠ 0 := by
  cases h : firstExitSite s.1 x with
  | none =>
    rw [idlaStep_of_none h]
    exact hs
  | some b =>
    by_cases hb : b ∈ Θ'
    · rw [idlaStep_of_some_mem h hb]
      intro c hc
      obtain ⟨a, ha, hac⟩ := hs c hc
      exact ⟨a, subset_union_left ha, hac⟩
    · rw [idlaStep_of_some_not_mem h hb]
      intro c hc
      rcases List.mem_append.1 hc with hc | hc
      · exact hs c hc
      · rw [List.mem_singleton] at hc
        rw [hc]
        obtain ⟨N, hN, hbA, hlt⟩ := exists_of_firstExitSite_eq_some h
        cases N with
        | zero =>
          have h0 : x 0 ∈ Θ' := hx0.resolve_left (by rw [hN]; exact hbA)
          rw [hN] at h0
          exact absurd h0 hb
        | succ k =>
          have hk : x k ∈ s.1 := hlt k (Nat.lt_succ_self k)
          rcases hx k with he | he
          · rw [← he, hN] at hk
            exact absurd hk hbA
          · rw [hN] at he
            exact ⟨x k, hk, he⟩

/-- Walkers started at `z ∈ s.1 ∪ Θ'` and moving along edges: every stopped position is joined by an edge to the
aggregate. -/
theorem foldl_idlaStep_stopped_adj (m : ℤ → ℤ → ℕ) {Θ' : Set ℤ} (z : ℤ) :
    ∀ (xs : List (ℕ → ℤ)) (s : Set ℤ × List ℤ),
      (∀ x ∈ xs, x 0 = z ∧ ∀ n, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0) → z ∈ s.1 ∪ Θ' →
      (∀ b ∈ s.2, ∃ a ∈ s.1, m a b ≠ 0) →
      ∀ b ∈ (xs.foldl (idlaStep Θ') s).2, ∃ a ∈ (xs.foldl (idlaStep Θ') s).1, m a b ≠ 0
  | [], _, _, _, hs => hs
  | x :: xs, s, hxs, hz, hs => by
    rw [List.foldl_cons]
    have hx := hxs x (by simp)
    refine foldl_idlaStep_stopped_adj m z xs _ (fun y hy => hxs y (by simp [hy])) ?_ ?_
    · rcases hz with hz | hz
      · exact Or.inl (idlaStep_fst_subset Θ' s x hz)
      · exact Or.inr hz
    · exact idlaStep_stopped_adj m (by rw [hx.1]; exact hz) hx.2 hs

end MatedCRT
