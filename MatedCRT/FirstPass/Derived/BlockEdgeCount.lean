import MatedCRT.Defs.Map
import MatedCRT.FirstPass.Derived.BlockVisiblePairs

/-!
# Edges of the mated-CRT map inside a block of cells

For a continuous path `X` and a cell size `ε > 0`, write `bmCellMin ε X k` for the minimum of `X` over the time
interval `[εk - ε, εk]` of the cell `k`. For `j < k` the adjacency condition (eq:edge-map) of Definition 1.1 says
exactly that the cell minima at `j` and at `k` are at most every cell minimum strictly between them
(`bmAdjacent_iff_forall_cellMin`): the interval `[εj, εk - ε]` is the union of the cells `j + 1, …, k - 1`, and for
`k = j + 1` it is the common endpoint `εj` of the two cells. So `(j, k)` is an edge for `X` if and only if it is a
visible pair of the cell minima.

Consequences for a block `[lo, hi]` of cells on which the cell minima of `L` and of `R` are pairwise distinct:
* `sum_bmEdgeCount_add_card_records`: the number of edges with both endpoints in the block plus the numbers of strict
  prefix and strict suffix minima of the two sequences of cell minima is `3 · #[lo, hi] + 1`
  (a consecutive pair carries one edge, a non-consecutive pair one edge for each path for which it is visible);
* `mem_records_of_bmEdgeCount_ne_zero`: an edge from a cell of the block to a cell outside it starts at a strict
  prefix or suffix minimum of the cell minima of `L` or of `R`.

Together with `card_blockVisiblePairs_add_card_prefixMins_add_card_suffixMins` this replaces the Euler formula in
the edge count of Berestycki–Gwynne, Lemma A.7.
-/

open Finset

namespace MatedCRT

/-- The minimum of the path `X` over the time interval `[εk - ε, εk]` of the cell `k`. -/
noncomputable def bmCellMin (ε : ℝ) (X : ℝ → ℝ) (k : ℤ) : ℝ :=
  sInf (X '' Set.Icc (ε * k - ε) (ε * k))

/-- The ordered pairs `j < k` of indices of the block `[lo, hi]`. -/
def blockPairs (lo hi : ℤ) : Finset (ℤ × ℤ) :=
  (Icc lo hi ×ˢ Icc lo hi).filter fun p => p.1 < p.2

theorem mem_blockPairs {lo hi j k : ℤ} :
    (j, k) ∈ blockPairs lo hi ↔ j ∈ Icc lo hi ∧ k ∈ Icc lo hi ∧ j < k := by
  simp only [blockPairs, mem_filter, mem_product, and_assoc]

theorem bmCellMin_le {ε : ℝ} {X : ℝ → ℝ} (hX : Continuous X) {k : ℤ} {t : ℝ}
    (ht : t ∈ Set.Icc (ε * k - ε) (ε * k)) : bmCellMin ε X k ≤ X t :=
  csInf_le (isCompact_Icc.image hX).bddBelow (Set.mem_image_of_mem X ht)

/-- **The adjacency condition through cell minima.** For `j < k` and a continuous path, the condition
(eq:edge-map) holds if and only if both cell minima at `j` and at `k` are at most every cell minimum strictly
between them. -/
theorem bmAdjacent_iff_forall_cellMin {ε : ℝ} (hε : 0 < ε) {X : ℝ → ℝ} (hX : Continuous X) {j k : ℤ}
    (hjk : j < k) :
    bmAdjacent ε X j k ↔ ∀ i : ℤ, j < i → i < k →
      sInf (X '' Set.Icc (ε * j - ε) (ε * j)) ≤ sInf (X '' Set.Icc (ε * i - ε) (ε * i)) ∧
      sInf (X '' Set.Icc (ε * k - ε) (ε * k)) ≤ sInf (X '' Set.Icc (ε * i - ε) (ε * i)) := by
  unfold bmAdjacent
  have hjk' : (j : ℝ) + 1 ≤ k := by exact_mod_cast hjk
  have hεjk : ε * ((j : ℝ) + 1) ≤ ε * k := mul_le_mul_of_nonneg_left hjk' hε.le
  constructor
  · intro h i hji hik
    have hji' : (j : ℝ) + 1 ≤ i := by exact_mod_cast hji
    have hik' : (i : ℝ) + 1 ≤ k := by exact_mod_cast hik
    have h1 : ε * ((j : ℝ) + 1) ≤ ε * i := mul_le_mul_of_nonneg_left hji' hε.le
    have h2 : ε * ((i : ℝ) + 1) ≤ ε * k := mul_le_mul_of_nonneg_left hik' hε.le
    have hsub : Set.Icc (ε * i - ε) (ε * i) ⊆ Set.Icc (ε * j) (ε * k - ε) :=
      Set.Icc_subset_Icc (by linarith) (by linarith)
    have hle : sInf (X '' Set.Icc (ε * j) (ε * k - ε)) ≤ sInf (X '' Set.Icc (ε * i - ε) (ε * i)) :=
      csInf_le_csInf (isCompact_Icc.image hX).bddBelow
        ((Set.nonempty_Icc.2 (by linarith)).image X) (Set.image_mono hsub)
    exact ⟨(le_max_left _ _).trans (h.trans hle), (le_max_right _ _).trans (h.trans hle)⟩
  · intro h
    refine le_csInf ((Set.nonempty_Icc.2 (by linarith)).image X) ?_
    rintro _ ⟨t, ⟨ht1, ht2⟩, rfl⟩
    rcases eq_or_lt_of_le (show j + 1 ≤ k from hjk) with hk | hk
    · -- `k = j + 1`: the interval is the common endpoint `εj` of the two cells
      have hkr : ε * (k : ℝ) = ε * j + ε := by rw [← hk]; push_cast; ring
      exact max_le (bmCellMin_le hX ⟨by linarith, by linarith⟩) (bmCellMin_le hX ⟨by linarith, by linarith⟩)
    · -- `k ≥ j + 2`: `t` lies in the cell `i = max (j + 1) ⌈t / ε⌉` with `j < i < k`
      have hc1 : t ≤ ε * (⌈t / ε⌉ : ℝ) := by
        have := Int.le_ceil (t / ε)
        rw [div_le_iff₀ hε] at this
        linarith
      have hc2 : ε * (⌈t / ε⌉ : ℝ) - ε < t := by
        have := Int.ceil_lt_add_one (t / ε)
        have h' : ((⌈t / ε⌉ : ℝ) - 1) < t / ε := by linarith
        rw [lt_div_iff₀ hε] at h'
        linarith
      have hck : ⌈t / ε⌉ ≤ k - 1 := by
        rw [Int.ceil_le, div_le_iff₀ hε]
        push_cast
        linarith
      have hji : j < max (j + 1) ⌈t / ε⌉ := lt_of_lt_of_le (lt_add_one j) (le_max_left _ _)
      have hik : max (j + 1) ⌈t / ε⌉ < k := max_lt hk (by omega)
      have hti : t ∈ Set.Icc (ε * ((max (j + 1) ⌈t / ε⌉ : ℤ) : ℝ) - ε) (ε * ((max (j + 1) ⌈t / ε⌉ : ℤ) : ℝ)) := by
        rcases le_total (j + 1) ⌈t / ε⌉ with hm | hm
        · rw [max_eq_right hm]
          exact ⟨hc2.le, hc1⟩
        · rw [max_eq_left hm]
          have hm' : (⌈t / ε⌉ : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast hm
          have := mul_le_mul_of_nonneg_left hm' hε.le
          push_cast
          constructor <;> nlinarith
      exact max_le ((h _ hji hik).1.trans (bmCellMin_le hX hti))
        ((h _ hji hik).2.trans (bmCellMin_le hX hti))

/-- For `j < k` in the block, the adjacency condition is visibility of the pair for the cell minima. -/
theorem bmAdjacent_iff_mem_blockVisiblePairs {ε : ℝ} (hε : 0 < ε) {X : ℝ → ℝ} (hX : Continuous X)
    {lo hi j k : ℤ} (hj : j ∈ Icc lo hi) (hk : k ∈ Icc lo hi) (hjk : j < k) :
    bmAdjacent ε X j k ↔ (j, k) ∈ blockVisiblePairs (bmCellMin ε X) lo hi := by
  rw [bmAdjacent_iff_forall_cellMin hε hX hjk, mem_blockVisiblePairs]
  exact ⟨fun h => ⟨hj, hk, hjk, h⟩, fun h => h.2.2.2⟩

open Classical in
theorem filter_blockPairs_bmAdjacent {ε : ℝ} (hε : 0 < ε) {X : ℝ → ℝ} (hX : Continuous X) (lo hi : ℤ) :
    (blockPairs lo hi).filter (fun p => bmAdjacent ε X p.1 p.2) =
      blockVisiblePairs (bmCellMin ε X) lo hi := by
  ext ⟨j, k⟩
  rw [mem_filter, mem_blockPairs]
  constructor
  · rintro ⟨⟨hj, hk, hjk⟩, hadj⟩
    exact (bmAdjacent_iff_mem_blockVisiblePairs hε hX hj hk hjk).1 hadj
  · intro h
    obtain ⟨hj, hk, hjk, -⟩ := mem_blockVisiblePairs.1 h
    exact ⟨⟨hj, hk, hjk⟩, (bmAdjacent_iff_mem_blockVisiblePairs hε hX hj hk hjk).2 h⟩

open Classical in
/-- A consecutive pair carries one edge; a non-consecutive pair carries one edge for each of `L`, `R` for
which (eq:edge-map) holds. -/
theorem bmEdgeCount_add_ite_eq {ε : ℝ} (hε : 0 < ε) {L R : ℝ → ℝ} (hL : Continuous L) (hR : Continuous R)
    {j k : ℤ} (hjk : j < k) :
    bmEdgeCount ε L R j k + (if k = j + 1 then 1 else 0) =
      (if bmAdjacent ε L j k then 1 else 0) + (if bmAdjacent ε R j k then 1 else 0) := by
  have hne : j ≠ k := hjk.ne
  have hmin : min j k = j := min_eq_left hjk.le
  have hmax : max j k = k := max_eq_right hjk.le
  simp only [bmEdgeCount, hne, ↓reduceIte, hmin, hmax]
  rcases eq_or_lt_of_le (show j + 1 ≤ k from hjk) with h | h
  · subst h
    have hL' := (bmAdjacent_iff_forall_cellMin hε hL hjk).2 fun i h1 h2 => by omega
    have hR' := (bmAdjacent_iff_forall_cellMin hε hR hjk).2 fun i h1 h2 => by omega
    simp [hL', hR']
  · have h1 : 1 < k - j := by omega
    have h2 : k ≠ j + 1 := by omega
    by_cases hL' : bmAdjacent ε L j k <;> by_cases hR' : bmAdjacent ε R j k <;> simp [hL', hR', h1, h2]

open Classical in
theorem card_filter_blockPairs_consecutive (lo hi : ℤ) :
    #((blockPairs lo hi).filter fun p => p.2 = p.1 + 1) = #(Icc lo (hi - 1)) := by
  refine card_nbij' Prod.fst (fun j => (j, j + 1)) ?_ ?_ ?_ ?_
  · rintro ⟨j, k⟩ h
    simp only [mem_coe, mem_filter, mem_blockPairs, mem_Icc] at h ⊢
    omega
  · intro j h
    simp only [mem_coe, mem_filter, mem_blockPairs, mem_Icc, and_true] at h ⊢
    omega
  · rintro ⟨j, k⟩ h
    simp only [mem_coe, mem_filter] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  · intro j _
    rfl

open Classical in
/-- **Edges inside a block of cells.** If the cell minima of `L` and of `R` are pairwise distinct on the block
`[lo, hi]` (`lo ≤ hi`), the number of edges with both endpoints in the block plus the numbers of strict prefix and
strict suffix minima of the two sequences of cell minima is `3 · #[lo, hi] + 1`. -/
theorem sum_bmEdgeCount_add_card_records {ε : ℝ} (hε : 0 < ε) {L R : ℝ → ℝ} (hL : Continuous L)
    (hR : Continuous R) {lo hi : ℤ} (hlohi : lo ≤ hi)
    (hinjL : Set.InjOn (bmCellMin ε L) (Icc lo hi : Set ℤ))
    (hinjR : Set.InjOn (bmCellMin ε R) (Icc lo hi : Set ℤ)) :
    (∑ p ∈ blockPairs lo hi, bmEdgeCount ε L R p.1 p.2) +
      (#(blockPrefixMins (bmCellMin ε L) lo hi) + #(blockSuffixMins (bmCellMin ε L) lo hi) +
        #(blockPrefixMins (bmCellMin ε R) lo hi) + #(blockSuffixMins (bmCellMin ε R) lo hi)) =
      3 * #(Icc lo hi) + 1 := by
  have key : (∑ p ∈ blockPairs lo hi, bmEdgeCount ε L R p.1 p.2) +
      #((blockPairs lo hi).filter fun p => p.2 = p.1 + 1) =
      #((blockPairs lo hi).filter fun p => bmAdjacent ε L p.1 p.2) +
        #((blockPairs lo hi).filter fun p => bmAdjacent ε R p.1 p.2) := by
    simp only [card_filter, ← sum_add_distrib]
    refine sum_congr rfl fun p hp => ?_
    obtain ⟨j, k⟩ := p
    exact bmEdgeCount_add_ite_eq hε hL hR (mem_blockPairs.1 hp).2.2
  rw [filter_blockPairs_bmAdjacent hε hL, filter_blockPairs_bmAdjacent hε hR,
    card_filter_blockPairs_consecutive] at key
  have hL2 := card_blockVisiblePairs_add_card_prefixMins_add_card_suffixMins hinjL
  have hR2 := card_blockVisiblePairs_add_card_prefixMins_add_card_suffixMins hinjR
  have hc : #(Icc lo (hi - 1)) + 1 = #(Icc lo hi) := by
    simp only [Int.card_Icc]
    omega
  omega

open Classical in
/-- **Edges inside a block of `N ≥ 1` cells.** For the block `[a + 1, a + N]`, the number of inner edges plus
the numbers of strict prefix and suffix minima of the two sequences of cell minima is `3N + 1`. -/
theorem sum_bmEdgeCount_add_card_records_of_length {ε : ℝ} (hε : 0 < ε) {L R : ℝ → ℝ}
    (hL : Continuous L) (hR : Continuous R) (a : ℤ) {N : ℕ} (hN : 1 ≤ N)
    (hinjL : Set.InjOn (bmCellMin ε L) (Icc (a + 1) (a + N) : Set ℤ))
    (hinjR : Set.InjOn (bmCellMin ε R) (Icc (a + 1) (a + N) : Set ℤ)) :
    (∑ p ∈ blockPairs (a + 1) (a + N), bmEdgeCount ε L R p.1 p.2) +
      (#(blockPrefixMins (bmCellMin ε L) (a + 1) (a + N)) +
        #(blockSuffixMins (bmCellMin ε L) (a + 1) (a + N)) +
        #(blockPrefixMins (bmCellMin ε R) (a + 1) (a + N)) +
        #(blockSuffixMins (bmCellMin ε R) (a + 1) (a + N))) = 3 * N + 1 := by
  rw [sum_bmEdgeCount_add_card_records hε hL hR (by omega) hinjL hinjR, Int.card_Icc]
  omega

/-- If (eq:edge-map) holds for `X` between a cell `k` of the block `[lo, hi]` and a cell `i` outside it, then `k`
is a strict prefix minimum (for `i < lo`) or a strict suffix minimum (for `i > hi`) of the cell minima of `X`. -/
theorem mem_blockRecords_of_bmAdjacent {ε : ℝ} (hε : 0 < ε) {X : ℝ → ℝ} (hX : Continuous X)
    {lo hi k i : ℤ} (hk : k ∈ Icc lo hi) (hio : i ∉ Icc lo hi)
    (hinj : Set.InjOn (bmCellMin ε X) (Icc lo hi : Set ℤ))
    (hadj : bmAdjacent ε X (min k i) (max k i)) :
    k ∈ blockPrefixMins (bmCellMin ε X) lo hi ∨ k ∈ blockSuffixMins (bmCellMin ε X) lo hi := by
  have hk' := hk
  rw [mem_Icc] at hk hio
  rcases lt_or_gt_of_ne (show k ≠ i by rintro rfl; exact hio hk) with hki | hki
  · right
    rw [min_eq_left hki.le, max_eq_right hki.le, bmAdjacent_iff_forall_cellMin hε hX hki] at hadj
    simp only [blockSuffixMins, mem_filter]
    refine ⟨hk', fun l hl hkl => ?_⟩
    have hl' := hl
    rw [mem_Icc] at hl
    exact lt_of_le_of_ne (hadj l hkl (by omega)).1
      fun h => hkl.ne (hinj (mem_coe.2 hk') (mem_coe.2 hl') h)
  · left
    rw [min_eq_right hki.le, max_eq_left hki.le, bmAdjacent_iff_forall_cellMin hε hX hki] at hadj
    simp only [blockPrefixMins, mem_filter]
    refine ⟨hk', fun l hl hlk => ?_⟩
    have hl' := hl
    rw [mem_Icc] at hl
    exact lt_of_le_of_ne (hadj l (by omega) hlk).2
      fun h => hlk.ne' (hinj (mem_coe.2 hk') (mem_coe.2 hl') h)

/-- **Edges leaving a block start at records.** If the cell minima of `L` and of `R` are pairwise distinct on the
block `[lo, hi]`, every edge from a cell `k` of the block to a cell `i` outside it starts at a strict prefix or
suffix minimum of the cell minima of `L` or of `R`. -/
theorem mem_records_of_bmEdgeCount_ne_zero {ε : ℝ} (hε : 0 < ε) {L R : ℝ → ℝ} (hL : Continuous L)
    (hR : Continuous R) {lo hi k i : ℤ} (hk : k ∈ Icc lo hi) (hio : i ∉ Icc lo hi)
    (hinjL : Set.InjOn (bmCellMin ε L) (Icc lo hi : Set ℤ))
    (hinjR : Set.InjOn (bmCellMin ε R) (Icc lo hi : Set ℤ))
    (hedge : bmEdgeCount ε L R k i ≠ 0) :
    (k ∈ blockPrefixMins (bmCellMin ε L) lo hi ∨ k ∈ blockSuffixMins (bmCellMin ε L) lo hi) ∨
      (k ∈ blockPrefixMins (bmCellMin ε R) lo hi ∨ k ∈ blockSuffixMins (bmCellMin ε R) lo hi) := by
  have hadj : bmAdjacent ε L (min k i) (max k i) ∨ bmAdjacent ε R (min k i) (max k i) := by
    by_contra h
    apply hedge
    simp only [bmEdgeCount]
    split_ifs <;> simp_all
  rcases hadj with h | h
  · exact Or.inl (mem_blockRecords_of_bmAdjacent hε hL hk hio hinjL h)
  · exact Or.inr (mem_blockRecords_of_bmAdjacent hε hR hk hio hinjR h)

end MatedCRT
