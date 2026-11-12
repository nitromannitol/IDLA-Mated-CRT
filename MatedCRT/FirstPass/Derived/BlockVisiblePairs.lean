import Mathlib

/-!
# Visible pairs and records of a finite block of distinct values

For values `m : ℤ → ℝ` on a block `B = [lo, hi]` of integers, a pair `j < k` in `B` is *visible* when
every value strictly between them is at least `m j` and at least `m k`. For the cell minima of a
Brownian path these are the pairs of cells of the block which are adjacent in the mated-CRT map through
that path (BG20, eq. (1.3)); consecutive pairs are always visible. A *prefix minimum* is a `k ∈ B` with
`m k < m i` for every earlier `i ∈ B`, a *suffix minimum* one with `m k < m i` for every later `i ∈ B`.

If the values are pairwise distinct on `B`, then
`#visible pairs + #prefix minima + #suffix minima = 2 #B`:
a visible pair with `m j < m k` is determined by `k`, which is not a prefix minimum, and `j` is the
nearest earlier index with a smaller value; symmetrically when `m k < m j`. This count replaces the
Euler formula for the triangulation formed by a block of cells in BG20 Lemma A.7.

* `blockVisiblePairs`, `blockPrefixMins`, `blockSuffixMins`;
* `card_blockVisiblePairs_add_card_prefixMins_add_card_suffixMins`;
* `card_blockVisiblePairs_add_of_length`: the same for `B = [a+1, a+N]`, with right side `2N`.
-/

open Finset

namespace MatedCRT

open Classical in
/-- The *visible pairs* `j < k` of the block `[lo, hi]` for the values `m`: every value strictly
between them is at least `m j` and at least `m k`. -/
noncomputable def blockVisiblePairs (m : ℤ → ℝ) (lo hi : ℤ) : Finset (ℤ × ℤ) :=
  (Icc lo hi ×ˢ Icc lo hi).filter fun p =>
    p.1 < p.2 ∧ ∀ i, p.1 < i → i < p.2 → m p.1 ≤ m i ∧ m p.2 ≤ m i

open Classical in
/-- The strict *prefix minima* of the block `[lo, hi]` for the values `m`. -/
noncomputable def blockPrefixMins (m : ℤ → ℝ) (lo hi : ℤ) : Finset ℤ :=
  (Icc lo hi).filter fun k => ∀ i ∈ Icc lo hi, i < k → m k < m i

open Classical in
/-- The strict *suffix minima* of the block `[lo, hi]` for the values `m`. -/
noncomputable def blockSuffixMins (m : ℤ → ℝ) (lo hi : ℤ) : Finset ℤ :=
  (Icc lo hi).filter fun k => ∀ i ∈ Icc lo hi, k < i → m k < m i

theorem mem_blockVisiblePairs {m : ℤ → ℝ} {lo hi j k : ℤ} :
    (j, k) ∈ blockVisiblePairs m lo hi ↔ j ∈ Icc lo hi ∧ k ∈ Icc lo hi ∧ j < k ∧
      ∀ i, j < i → i < k → m j ≤ m i ∧ m k ≤ m i := by
  simp only [blockVisiblePairs, mem_filter, mem_product, and_assoc]

/-- Visible pairs whose left value is the smaller one are counted by their right endpoints, which are
exactly the indices of the block that are not prefix minima. -/
theorem card_visiblePairs_lt_add_card_prefixMins {m : ℤ → ℝ} {lo hi : ℤ}
    (hinj : Set.InjOn m (Icc lo hi : Set ℤ)) :
    #((blockVisiblePairs m lo hi).filter fun p => m p.1 < m p.2) + #(blockPrefixMins m lo hi) =
      #(Icc lo hi) := by
  classical
  set G := (blockVisiblePairs m lo hi).filter fun p => m p.1 < m p.2 with hG
  have hmemG : ∀ j k, (j, k) ∈ G ↔ j ∈ Icc lo hi ∧ k ∈ Icc lo hi ∧ j < k ∧
      (∀ i, j < i → i < k → m j ≤ m i ∧ m k ≤ m i) ∧ m j < m k := by
    intro j k
    rw [hG, mem_filter, mem_blockVisiblePairs]
    tauto
  have hinjG : Set.InjOn Prod.snd (G : Set (ℤ × ℤ)) := by
    rintro ⟨j, k⟩ hp ⟨j', k'⟩ hp' (hkk : k = k')
    subst hkk
    obtain ⟨hj, -, hjk, hvis, hlt⟩ := (hmemG j k).1 hp
    obtain ⟨hj', -, hjk', hvis', hlt'⟩ := (hmemG j' k).1 hp'
    rcases lt_trichotomy j j' with h | h | h
    · exact absurd ((hvis j' h hjk').2) (not_le.2 hlt')
    · rw [h]
    · exact absurd ((hvis' j h hjk).2) (not_le.2 hlt)
  have himg : G.image Prod.snd = Icc lo hi \ blockPrefixMins m lo hi := by
    ext k
    simp only [mem_image, mem_sdiff, blockPrefixMins, mem_filter, not_and, not_forall, not_lt,
      exists_prop]
    constructor
    · rintro ⟨⟨j, k'⟩, hp, rfl⟩
      obtain ⟨hj, hk, hjk, -, hlt⟩ := (hmemG j k').1 hp
      exact ⟨hk, fun _ => ⟨j, hj, hjk, hlt.le⟩⟩
    · rintro ⟨hk, hnot⟩
      obtain ⟨i, hiB0, hik, hle⟩ := hnot hk
      have hne : m i ≠ m k := fun h => (ne_of_lt hik) (hinj (mem_coe.2 hiB0) (mem_coe.2 hk) h)
      set T := (Icc lo hi).filter fun i => i < k ∧ m i < m k with hT
      have hTne : T.Nonempty := ⟨i, mem_filter.2 ⟨hiB0, hik, lt_of_le_of_ne hle hne⟩⟩
      obtain ⟨hjB, hjk, hjlt⟩ : T.max' hTne ∈ Icc lo hi ∧ T.max' hTne < k ∧ m (T.max' hTne) < m k := by
        have h : T.max' hTne ∈ (Icc lo hi).filter fun i => i < k ∧ m i < m k := T.max'_mem hTne
        rw [mem_filter] at h
        exact ⟨h.1, h.2⟩
      refine ⟨(T.max' hTne, k), (hmemG _ _).2 ⟨hjB, hk, hjk, fun i hji hik => ?_, hjlt⟩, rfl⟩
      have hiB : i ∈ Icc lo hi := by
        rw [mem_Icc] at hjB hk ⊢
        exact ⟨by omega, by omega⟩
      have hmk : m k ≤ m i := by
        by_contra hlt
        have hiT : i ∈ T := mem_filter.2 ⟨hiB, hik, not_le.1 hlt⟩
        exact absurd (T.le_max' i hiT) (not_le.2 hji)
      exact ⟨(hjlt.trans_le hmk).le, hmk⟩
  rw [← card_image_of_injOn hinjG, himg]
  exact card_sdiff_add_card_eq_card (filter_subset _ _)

/-- Visible pairs whose right value is the smaller one are counted by their left endpoints, which are
exactly the indices of the block that are not suffix minima. -/
theorem card_visiblePairs_not_lt_add_card_suffixMins {m : ℤ → ℝ} {lo hi : ℤ}
    (hinj : Set.InjOn m (Icc lo hi : Set ℤ)) :
    #((blockVisiblePairs m lo hi).filter fun p => ¬ m p.1 < m p.2) + #(blockSuffixMins m lo hi) =
      #(Icc lo hi) := by
  classical
  set G := (blockVisiblePairs m lo hi).filter fun p => ¬ m p.1 < m p.2 with hG
  have hmemG : ∀ j k, (j, k) ∈ G ↔ j ∈ Icc lo hi ∧ k ∈ Icc lo hi ∧ j < k ∧
      (∀ i, j < i → i < k → m j ≤ m i ∧ m k ≤ m i) ∧ ¬ m j < m k := by
    intro j k
    rw [hG, mem_filter, mem_blockVisiblePairs]
    tauto
  have hgt : ∀ j k, (j, k) ∈ G → m k < m j := by
    intro j k hp
    obtain ⟨hj, hk, hjk, -, hnlt⟩ := (hmemG j k).1 hp
    have hne : m j ≠ m k := fun h => (ne_of_lt hjk) (hinj (mem_coe.2 hj) (mem_coe.2 hk) h)
    exact lt_of_le_of_ne (not_lt.1 hnlt) hne.symm
  have hinjG : Set.InjOn Prod.fst (G : Set (ℤ × ℤ)) := by
    rintro ⟨j, k⟩ hp ⟨j', k'⟩ hp' (hjj : j = j')
    subst hjj
    obtain ⟨-, -, hjk, hvis, -⟩ := (hmemG j k).1 hp
    obtain ⟨-, -, hjk', hvis', -⟩ := (hmemG j k').1 hp'
    rcases lt_trichotomy k k' with h | h | h
    · exact absurd ((hvis' k hjk h).1) (not_le.2 (hgt j k hp))
    · rw [h]
    · exact absurd ((hvis k' hjk' h).1) (not_le.2 (hgt j k' hp'))
  have himg : G.image Prod.fst = Icc lo hi \ blockSuffixMins m lo hi := by
    ext j
    simp only [mem_image, mem_sdiff, blockSuffixMins, mem_filter, not_and, not_forall, not_lt,
      exists_prop]
    constructor
    · rintro ⟨⟨j', k⟩, hp, rfl⟩
      obtain ⟨hj, hk, hjk, -, -⟩ := (hmemG j' k).1 hp
      exact ⟨hj, fun _ => ⟨k, hk, hjk, (hgt j' k hp).le⟩⟩
    · rintro ⟨hj, hnot⟩
      obtain ⟨i, hiB0, hji, hle⟩ := hnot hj
      have hne : m i ≠ m j := fun h => (ne_of_lt hji).symm (hinj (mem_coe.2 hiB0) (mem_coe.2 hj) h)
      set T := (Icc lo hi).filter fun i => j < i ∧ m i < m j with hT
      have hTne : T.Nonempty := ⟨i, mem_filter.2 ⟨hiB0, hji, lt_of_le_of_ne hle hne⟩⟩
      obtain ⟨hkB, hjk, hklt⟩ : T.min' hTne ∈ Icc lo hi ∧ j < T.min' hTne ∧ m (T.min' hTne) < m j := by
        have h : T.min' hTne ∈ (Icc lo hi).filter fun i => j < i ∧ m i < m j := T.min'_mem hTne
        rw [mem_filter] at h
        exact ⟨h.1, h.2⟩
      refine ⟨(j, T.min' hTne), (hmemG _ _).2 ⟨hj, hkB, hjk, fun i hji hik => ?_,
        not_lt.2 hklt.le⟩, rfl⟩
      have hiB : i ∈ Icc lo hi := by
        rw [mem_Icc] at hkB hj ⊢
        exact ⟨by omega, by omega⟩
      have hmj : m j ≤ m i := by
        by_contra hlt
        have hiT : i ∈ T := mem_filter.2 ⟨hiB, hji, not_le.1 hlt⟩
        exact absurd (T.min'_le i hiT) (not_le.2 hik)
      exact ⟨hmj, (hklt.trans_le hmj).le⟩
  rw [← card_image_of_injOn hinjG, himg]
  exact card_sdiff_add_card_eq_card (filter_subset _ _)

/-- **Visible pairs and records.** For values pairwise distinct on the block `[lo, hi]`,
`#visible pairs + #prefix minima + #suffix minima = 2 #[lo, hi]`. -/
theorem card_blockVisiblePairs_add_card_prefixMins_add_card_suffixMins {m : ℤ → ℝ} {lo hi : ℤ}
    (hinj : Set.InjOn m (Icc lo hi : Set ℤ)) :
    #(blockVisiblePairs m lo hi) + #(blockPrefixMins m lo hi) + #(blockSuffixMins m lo hi) =
      2 * #(Icc lo hi) := by
  have h1 := card_visiblePairs_lt_add_card_prefixMins hinj
  have h2 := card_visiblePairs_not_lt_add_card_suffixMins hinj
  have h3 := card_filter_add_card_filter_not (s := blockVisiblePairs m lo hi)
    (p := fun p => m p.1 < m p.2)
  omega

/-- **Visible pairs and records of a block of `N` indices.** For values pairwise distinct on
`[a+1, a+N]`, `#visible pairs + #prefix minima + #suffix minima = 2N`. -/
theorem card_blockVisiblePairs_add_of_length {m : ℤ → ℝ} (a : ℤ) (N : ℕ)
    (hinj : Set.InjOn m (Icc (a + 1) (a + N) : Set ℤ)) :
    #(blockVisiblePairs m (a + 1) (a + N)) + #(blockPrefixMins m (a + 1) (a + N)) +
      #(blockSuffixMins m (a + 1) (a + N)) = 2 * N := by
  rw [card_blockVisiblePairs_add_card_prefixMins_add_card_suffixMins hinj, Int.card_Icc]
  congr 1
  omega

end MatedCRT
