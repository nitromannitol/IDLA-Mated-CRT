import MatedCRT.FirstPass.Derived.BlockDegreeSum
import MatedCRT.FirstPass.Derived.BlockRunningMinima
import MatedCRT.Defs.Setting

/-!
# Degree sum of a block of cells and running minima of the boundary-length paths

Berestycki–Gwynne (2020), Appendix A, (A.34) and (A.43): the degree sum over a block `[a + 1, a + N]`
of `N` cells of the mated-CRT map differs from `6N` by at most `2 + (2 + D) K`, where `D` bounds the
degrees on the block and `K` is the total number of cells of the block containing a running minimum,
relative to the start of the block, of one of the four paths `L`, `R` and their time reversals on the
block.

## Main results

* `abs_sum_mdeg_block_sub_le_runningMin`: the deterministic bound for continuous `L, R`;
* `MatedCRTEnv.abs_sum_matedDeg_block_sub_le_runningMin`: the same bound for the mated-CRT map of an
  environment, for every `ω` of the full-measure event on which the edge multiplicities are locally
  finite.
-/

open Finset MeasureTheory

namespace MatedCRT

/-- The time reversal `t ↦ X (ε (lo + hi - 1) - t)` of a path on the block `[lo, hi]` of cells of
size `ε`: it maps the cell `k` onto the cell `lo + hi - k`. -/
noncomputable def blockReversal (ε : ℝ) (X : ℝ → ℝ) (lo hi : ℤ) : ℝ → ℝ :=
  fun t => X (ε * ((lo + hi - 1 : ℤ) : ℝ) - t)

/-- The number of cells of the block `[lo, hi]` containing a running minimum of `L`, of `R`, or of
their time reversals on the block (BG20 (A.34), four terms). -/
noncomputable def blockRunningMinCount (ε : ℝ) (L R : ℝ → ℝ) (lo hi : ℤ) : ℕ :=
  #(blockRunningMinCells ε L lo hi) + #(blockRunningMinCells ε (blockReversal ε L lo hi) lo hi) +
    #(blockRunningMinCells ε R lo hi) + #(blockRunningMinCells ε (blockReversal ε R lo hi) lo hi)

/-- The total number of strict prefix and suffix minima of the two sequences of cell minima of a
block is at most the running-minimum count of the block. -/
theorem card_blockRecords_le_blockRunningMinCount {ε : ℝ} (hε : 0 < ε) {L R : ℝ → ℝ}
    (hL : Continuous L) (hR : Continuous R) (lo hi : ℤ) :
    #(blockPrefixMins (bmCellMin ε L) lo hi) + #(blockSuffixMins (bmCellMin ε L) lo hi) +
        #(blockPrefixMins (bmCellMin ε R) lo hi) + #(blockSuffixMins (bmCellMin ε R) lo hi) ≤
      blockRunningMinCount ε L R lo hi := by
  have h1 := card_blockPrefixMins_le_blockRunningMinCells hε hL lo hi
  have h2 := card_blockSuffixMins_le_blockRunningMinCells_reflect hε hL lo hi
  have h3 := card_blockPrefixMins_le_blockRunningMinCells hε hR lo hi
  have h4 := card_blockSuffixMins_le_blockRunningMinCells_reflect hε hR lo hi
  unfold blockRunningMinCount blockReversal
  omega

/-- **The degree sum of a block and running minima (BG20 (A.34), (A.43)).** For continuous `L, R`, a
locally finite map, a block `[a + 1, a + N]` of `N ≥ 1` cells with distinct cell minima for `L` and for
`R`, and degrees at most `D` on the block, the degree sum over the block differs from `6N` by at most
`2 + (2 + D) K`, `K` the running-minimum count of the block. -/
theorem abs_sum_mdeg_block_sub_le_runningMin {ε : ℝ} (hε : 0 < ε) {L R : ℝ → ℝ}
    (hL : Continuous L) (hR : Continuous R) (hlf : IsLocallyFiniteMult (bmEdgeCount ε L R))
    (a : ℤ) {N : ℕ} (hN : 1 ≤ N)
    (hinjL : Set.InjOn (bmCellMin ε L) (Icc (a + 1) (a + N) : Set ℤ))
    (hinjR : Set.InjOn (bmCellMin ε R) (Icc (a + 1) (a + N) : Set ℤ)) {D : ℝ}
    (hD : ∀ k ∈ Icc (a + 1) (a + N), (mdeg (bmEdgeCount ε L R) k : ℝ) ≤ D) :
    |∑ k ∈ Ioc a (a + N), (mdeg (bmEdgeCount ε L R) k : ℝ) - 6 * N| ≤
      2 + (2 + D) * (blockRunningMinCount ε L R (a + 1) (a + N) : ℝ) := by
  have h7 := abs_sum_mdeg_block_sub_le hε hL hR hlf a hN hinjL hinjR hD
  have hD0 : 0 ≤ D :=
    (Nat.cast_nonneg _).trans (hD (a + 1) (mem_Icc.2 ⟨le_rfl, by omega⟩))
  have hK := card_blockRecords_le_blockRunningMinCount hε hL hR (a + 1) (a + N)
  refine h7.trans ?_
  gcongr

/-- **The degree sum of a block of the mated-CRT map and running minima.** For every `ω` of the
full-measure event on which the edge multiplicities are locally finite (`hlf`), every block
`[a + 1, a + N]` of `N ≥ 1` cells on which the cell minima of the two boundary-length coordinates are
distinct and the degrees are at most `D` has degree sum within `2 + (2 + D) K` of `6N`, `K` the
running-minimum count of the block for the boundary-length pair `(L, R) = S.bm ω`. -/
theorem MatedCRTEnv.abs_sum_matedDeg_block_sub_le_runningMin {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) {ε : ℝ} (hε : 0 < ε) {ω : Ω} (hlf : IsLocallyFiniteMult (S.mult ε ω))
    (a : ℤ) {N : ℕ} (hN : 1 ≤ N)
    (hinjL : Set.InjOn (bmCellMin ε fun t => (S.bm ω t).1) (Icc (a + 1) (a + N) : Set ℤ))
    (hinjR : Set.InjOn (bmCellMin ε fun t => (S.bm ω t).2) (Icc (a + 1) (a + N) : Set ℤ))
    {D : ℝ} (hD : ∀ k ∈ Icc (a + 1) (a + N), (matedDeg (S.mult ε ω) k : ℝ) ≤ D) :
    |∑ k ∈ Ioc a (a + N), (matedDeg (S.mult ε ω) k : ℝ) - 6 * N| ≤
      2 + (2 + D) * (blockRunningMinCount ε (fun t => (S.bm ω t).1) (fun t => (S.bm ω t).2)
        (a + 1) (a + N) : ℝ) :=
  abs_sum_mdeg_block_sub_le_runningMin hε (continuous_fst.comp (S.bm ω).continuous)
    (continuous_snd.comp (S.bm ω).continuous) hlf a hN hinjL hinjR hD

end MatedCRT
