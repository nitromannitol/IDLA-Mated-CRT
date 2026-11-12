import MatedCRT.FirstPass.Derived.BlockEdgeCount
import MatedCRT.Proofs.Infra.MatingOfTrees
import MatedCRT.Proofs.Infra.DiscretePotential

/-!
# The degree sum of a block of cells (BG20 (A.43), deterministic part)

For the mated-CRT map `bmEdgeCount ε L R` of a pair of continuous paths, a block `[a + 1, a + N]` of
`N ≥ 1` cells whose cell minima are distinct for `L` and for `R`, and a bound `D` on the degrees of the
cells of the block, the degree sum of the block is within `2 + (2 + D) r` of `6N`, where `r` is the total
number of strict prefix and suffix minima of the two sequences of cell minima.

Indeed the degree sum is twice the number of inner edges plus the number of edges leaving the block. By
`sum_bmEdgeCount_add_card_records_of_length` the inner edges number `3N + 1 - r`; an edge leaves the block
only at a record cell (`mem_records_of_bmEdgeCount_ne_zero`), and each record cell carries at most `D`
edges. This replaces the Euler-formula count of BG20 (A.37)-(A.43): no planarity is used.
-/

open Finset

namespace MatedCRT

/-- The sum over a block of the edge multiplicities between its cells is twice the number of inner
edges (no loops, undirected). -/
theorem sum_sum_bmEdgeCount_block (ε : ℝ) (L R : ℝ → ℝ) (lo hi : ℤ) :
    ∑ k ∈ Icc lo hi, ∑ i ∈ Icc lo hi, bmEdgeCount ε L R k i =
      2 * ∑ p ∈ blockPairs lo hi, bmEdgeCount ε L R p.1 p.2 := by
  rw [← Finset.sum_product' (f := fun k i => bmEdgeCount ε L R k i),
    ← sum_filter_add_sum_filter_not (Icc lo hi ×ˢ Icc lo hi) (fun p : ℤ × ℤ => p.1 < p.2)]
  have h1 : (Icc lo hi ×ˢ Icc lo hi).filter (fun p : ℤ × ℤ => p.1 < p.2) = blockPairs lo hi := rfl
  rw [h1, two_mul]
  congr 1
  rw [← sum_filter_add_sum_filter_not
    ((Icc lo hi ×ˢ Icc lo hi).filter (fun p : ℤ × ℤ => ¬ p.1 < p.2)) (fun p : ℤ × ℤ => p.2 < p.1)]
  have h0 : ∑ p ∈ ((Icc lo hi ×ˢ Icc lo hi).filter (fun p : ℤ × ℤ => ¬ p.1 < p.2)).filter
      (fun p : ℤ × ℤ => ¬ p.2 < p.1), bmEdgeCount ε L R p.1 p.2 = 0 := by
    refine sum_eq_zero fun p hp => ?_
    simp only [mem_filter] at hp
    have : p.1 = p.2 := by omega
    rw [this, bmEdgeCount_self]
  rw [h0, add_zero]
  refine sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [blockPairs, mem_filter, mem_product, mem_Icc, Prod.fst_swap, Prod.snd_swap] at hp ⊢
    omega
  · intro p hp
    simp only [blockPairs, mem_filter, mem_product, mem_Icc, Prod.fst_swap, Prod.snd_swap] at hp ⊢
    omega
  · intro p _
    exact Prod.swap_swap p
  · intro p _
    exact Prod.swap_swap p
  · intro p _
    exact bmEdgeCount_symm ε L R p.1 p.2

/-- **The degree sum of a block (BG20 (A.43), deterministic form).** For continuous `L, R`, a locally
finite map, a block `[a + 1, a + N]` of `N ≥ 1` cells with distinct cell minima for `L` and for `R`, and
degrees at most `D` on the block, the degree sum over the block differs from `6N` by at most
`2 + (2 + D) r`, with `r` the total number of strict prefix and suffix minima of the two sequences of
cell minima on the block. -/
theorem abs_sum_mdeg_block_sub_le {ε : ℝ} (hε : 0 < ε) {L R : ℝ → ℝ} (hL : Continuous L)
    (hR : Continuous R) (hlf : IsLocallyFiniteMult (bmEdgeCount ε L R)) (a : ℤ) {N : ℕ}
    (hN : 1 ≤ N)
    (hinjL : Set.InjOn (bmCellMin ε L) (Icc (a + 1) (a + N) : Set ℤ))
    (hinjR : Set.InjOn (bmCellMin ε R) (Icc (a + 1) (a + N) : Set ℤ)) {D : ℝ}
    (hD : ∀ k ∈ Icc (a + 1) (a + N), (mdeg (bmEdgeCount ε L R) k : ℝ) ≤ D) :
    |∑ k ∈ Ioc a (a + N), (mdeg (bmEdgeCount ε L R) k : ℝ) - 6 * N| ≤
      2 + (2 + D) * ((#(blockPrefixMins (bmCellMin ε L) (a + 1) (a + N)) +
        #(blockSuffixMins (bmCellMin ε L) (a + 1) (a + N)) +
        #(blockPrefixMins (bmCellMin ε R) (a + 1) (a + N)) +
        #(blockSuffixMins (bmCellMin ε R) (a + 1) (a + N)) : ℕ) : ℝ) := by
  set m := bmEdgeCount ε L R with hm
  set B := Icc (a + 1) (a + (N : ℤ)) with hB
  set PL := blockPrefixMins (bmCellMin ε L) (a + 1) (a + N) with hPL
  set SL := blockSuffixMins (bmCellMin ε L) (a + 1) (a + N) with hSL
  set PR := blockPrefixMins (bmCellMin ε R) (a + 1) (a + N) with hPR
  set SR := blockSuffixMins (bmCellMin ε R) (a + 1) (a + N) with hSR
  set Rec := PL ∪ SL ∪ PR ∪ SR with hRec
  set r : ℕ := #PL + #SL + #PR + #SR with hr
  set E : ℕ := ∑ p ∈ blockPairs (a + 1) (a + N), m p.1 p.2 with hE
  set out : ℤ → ℕ := fun k => ∑ i ∈ (hlf k).toFinset \ B, m k i with hout
  have hBI : Ioc a (a + (N : ℤ)) = B := by
    ext k
    simp only [hB, mem_Ioc, mem_Icc]
    omega
  have hD0 : 0 ≤ D := (Nat.cast_nonneg _).trans (hD (a + 1) (mem_Icc.mpr ⟨le_rfl, by omega⟩))
  have hdeg : ∀ k, mdeg m k = ∑ i ∈ B, m k i + out k := by
    intro k
    rw [mdeg, finsum_eq_sum_of_support_subset (s := B ∪ ((hlf k).toFinset \ B)) _ ?_,
      sum_union disjoint_sdiff]
    intro i hi
    rw [Function.mem_support] at hi
    by_cases hiB : i ∈ B
    · exact mem_coe.mpr (mem_union_left _ hiB)
    · exact mem_coe.mpr (mem_union_right _ (mem_sdiff.mpr ⟨(hlf k).mem_toFinset.mpr hi, hiB⟩))
  have hout0 : ∀ k ∈ B, k ∉ Rec → out k = 0 := by
    intro k hk hkR
    refine sum_eq_zero fun i hi => ?_
    by_contra hne
    have hiB : i ∉ B := (mem_sdiff.mp hi).2
    rcases mem_records_of_bmEdgeCount_ne_zero hε hL hR hk hiB hinjL hinjR hne with (h | h) | (h | h)
    · exact hkR (mem_union_left _ (mem_union_left _ (mem_union_left _ h)))
    · exact hkR (mem_union_left _ (mem_union_left _ (mem_union_right _ h)))
    · exact hkR (mem_union_left _ (mem_union_right _ h))
    · exact hkR (mem_union_right _ h)
  have hout_le : ∀ k ∈ B, (out k : ℝ) ≤ D := by
    intro k hk
    have h1 : out k ≤ mdeg m k := by
      rw [hdeg k]
      exact Nat.le_add_left _ _
    exact (Nat.cast_le.mpr h1).trans (hD k hk)
  have hRec_card : #Rec ≤ r :=
    (card_union_le _ _).trans (Nat.add_le_add_right ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _)) _)
  have hO : (∑ k ∈ B, (out k : ℝ)) ≤ r * D := by
    calc ∑ k ∈ B, (out k : ℝ) = ∑ k ∈ B.filter (· ∈ Rec), (out k : ℝ) := by
          refine (sum_filter_of_ne fun k hk hne => ?_).symm
          by_contra h
          exact hne (by rw [hout0 k hk h, Nat.cast_zero])
      _ ≤ ∑ _k ∈ B.filter (· ∈ Rec), D := sum_le_sum fun k hk => hout_le k (mem_filter.mp hk).1
      _ = #(B.filter (· ∈ Rec)) * D := by rw [sum_const, nsmul_eq_mul]
      _ ≤ r * D := by
          refine mul_le_mul_of_nonneg_right ?_ hD0
          exact_mod_cast (card_le_card fun k hk => (mem_filter.mp hk).2).trans hRec_card
  have hO0 : 0 ≤ ∑ k ∈ B, (out k : ℝ) := sum_nonneg fun _ _ => Nat.cast_nonneg _
  have h2E : ∑ k ∈ B, ∑ i ∈ B, (m k i : ℝ) = 2 * (E : ℝ) := by
    have := congrArg (Nat.cast (R := ℝ)) (sum_sum_bmEdgeCount_block ε L R (a + 1) (a + N))
    push_cast at this
    rw [hE]
    push_cast
    exact this
  have htot : ∑ k ∈ B, (mdeg m k : ℝ) = 2 * (E : ℝ) + ∑ k ∈ B, (out k : ℝ) := by
    simp_rw [hdeg]
    push_cast
    rw [sum_add_distrib, h2E]
  have hEr : (E : ℝ) + r = 3 * N + 1 := by
    exact_mod_cast sum_bmEdgeCount_add_card_records_of_length hε hL hR a hN hinjL hinjR
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hrD : 0 ≤ (r : ℝ) * D := mul_nonneg hr0 hD0
  rw [hBI, htot, abs_le]
  constructor <;> nlinarith

end MatedCRT
