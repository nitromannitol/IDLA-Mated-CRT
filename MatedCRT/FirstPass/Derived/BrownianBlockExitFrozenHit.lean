import MatedCRT.FirstPass.Derived.BrownianBlockExitTightness
import MatedCRT.FirstPass.Derived.PlanarBrownianUnboundedRange

/-!
# Block exits of planar Brownian motion reach the frozen set

The block-exit times `σ_n` of `BrownianBlockExitTimes` read an infinite exit time as `0`. A path
with unbounded range exits every bounded set after every time, so along such a path each block
exit is a genuine exit: started off the frozen set `F`, the path leaves the open block of side
`3 s` around its current cell and moves by more than `s / 2`. Planar Brownian paths have unbounded
range almost surely, so the separated-chain bound of `BrownianBlockExitTightness` (with separation
`s / 2`) bounds the probability that the first `⌊r ^ (-(2 + ζ))⌋` block-exit positions all avoid
`F` while staying in a set `K` near the start.

## Main results

* `not_isBounded_range_shift`: unbounded range is preserved by every time shift.
* `exitTime_lt_top_of_not_isBounded`: a path with unbounded range exits every bounded set.
* `half_lt_norm_blockExit_step`: along a path with unbounded range, if `ω σ_n ∉ F` then
  `s / 2 < ‖ω σ_{n+1} - ω σ_n‖`.
* `planarBrownianMotion_blockExit_avoid_frozen_superpoly`: for `0 < ζ < 1` and `p` there is `C`
  such that `P_z(∀ n < ⌊r ^ (-(2 + ζ))⌋, ω σ_n ∉ F ∧ ω σ_n ∈ K) ≤ C r ^ p` whenever
  `0 < r < 1`, `4 a r ≤ s` and every point of `K` is at distance less than `a - 4 s` from `z`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric MarkovProcess
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

/-- A path with unbounded range, shifted by any time, still has unbounded range. -/
theorem not_isBounded_range_shift {ω : ContinuousPath ℂ}
    (hω : ¬ Bornology.IsBounded (range ω)) (T : ℝ≥0) :
    ¬ Bornology.IsBounded (range (ContinuousPath.shift T ω)) := by
  intro hb
  apply hω
  have hc : Bornology.IsBounded (ω '' Icc 0 T) :=
    (isCompact_Icc.image ω.continuous).isBounded
  refine (hc.union hb).subset ?_
  rintro _ ⟨t, rfl⟩
  by_cases ht : t ≤ T
  · exact Or.inl ⟨t, ⟨zero_le, ht⟩, rfl⟩
  · refine Or.inr ⟨t - T, ?_⟩
    rw [ContinuousPath.shift_apply, add_tsub_cancel_of_le (not_le.1 ht).le]

/-- A path with unbounded range exits every bounded set in finite time. -/
theorem exitTime_lt_top_of_not_isBounded {ω : ContinuousPath ℂ}
    (hω : ¬ Bornology.IsBounded (range ω)) {U : Set ℂ} (hU : Bornology.IsBounded U) :
    ContinuousPath.exitTime U ω < ⊤ := by
  rw [ContinuousPath.exitTime_lt_top_iff]
  by_contra h
  exact hω (hU.subset (range_subset_iff.2 fun t => not_not.1 fun ht => h ⟨t, ht⟩))

/-- Along a path with unbounded range started off the frozen set, the first block exit leaves
the open block around the starting cell, hence moves by more than `s / 2`. -/
theorem half_lt_norm_firstBlockExit {s : ℝ} (hs : 0 < s) {F : Set ℂ} {ω : ContinuousPath ℂ}
    (hω : ¬ Bornology.IsBounded (range ω)) (h0 : ω 0 ∉ F) :
    s / 2 < ‖ω (firstBlockExitTime s F ω) - ω 0‖ := by
  have hU := isOpen_openBlock s (cellIndex s (ω 0)).1 (cellIndex s (ω 0)).2
  have hfin := (exitTime_lt_top_of_not_isBounded hω
    (isBounded_openBlock s (cellIndex s (ω 0)).1 (cellIndex s (ω 0)).2)).ne
  have hfr := ContinuousPath.coordinate_exitTime_mem_frontier _ hU ω
    (mem_openBlock_cellIndex hs (ω 0)) hfin
  have heq : firstBlockExitTime s F ω = (ContinuousPath.exitTime
      (openBlock s (cellIndex s (ω 0)).1 (cellIndex s (ω 0)).2) ω).toNNReal := by
    simp only [firstBlockExitTime, h0, ↓reduceIte]
    rfl
  rw [hU.frontier_eq, ← heq] at hfr
  by_contra hle
  exact hfr.2 (closedBall_subset_openBlock hs (mem_closedCell_cellIndex hs (ω 0))
    (by rw [mem_closedBall, dist_eq_norm]; exact not_lt.1 hle))

/-- **Block exits are genuine steps.** Along a path with unbounded range, if the `n`-th
block-exit position lies off the frozen set, the next block-exit position is more than `s / 2`
away from it. -/
theorem half_lt_norm_blockExit_step {s : ℝ} (hs : 0 < s) {F : Set ℂ} {ω : ContinuousPath ℂ}
    (hω : ¬ Bornology.IsBounded (range ω)) (n : ℕ) (hn : ω (blockExitTimes s F n ω) ∉ F) :
    s / 2 < ‖ω (blockExitTimes s F (n + 1) ω) - ω (blockExitTimes s F n ω)‖ := by
  have h := half_lt_norm_firstBlockExit hs (F := F)
    (not_isBounded_range_shift hω (blockExitTimes s F n ω))
    (by rwa [ContinuousPath.shift_apply, add_zero])
  rwa [ContinuousPath.shift_apply, ContinuousPath.shift_apply, add_zero,
    ← blockExitTimes_succ'] at h

/-- **The block-exit chain reaches the frozen set.** For `0 < ζ < 1` and every `p` there is `C`
such that for every start `z`, mesh `s > 0`, frozen set `F`, set `K` all of whose points lie at
distance less than `a - 4 s` from `z`, and `0 < r < 1` with `4 a r ≤ s`, planar Brownian motion
from `z` keeps its first `⌊r ^ (-(2 + ζ))⌋` block-exit positions off `F` and inside `K` with
probability at most `C r ^ p`. -/
theorem planarBrownianMotion_blockExit_avoid_frozen_superpoly {ζ : ℝ} (hζ0 : 0 < ζ)
    (hζ1 : ζ < 1) (p : ℕ) :
    ∃ C : ℝ, ∀ (z : ℂ) (s : ℝ), 0 < s → ∀ (F K : Set ℂ) (a r : ℝ), 0 < a → 0 < r → r < 1 →
      4 * (a * r) ≤ s → (∀ y ∈ K, ‖y - z‖ < a - 4 * s) →
      planarBrownianMotion z {ω | ∀ n < ⌊r ^ (-(2 + ζ))⌋₊,
          ω (blockExitTimes s F n ω) ∉ F ∧ ω (blockExitTimes s F n ω) ∈ K}
        ≤ ENNReal.ofReal (C * r ^ p) := by
  obtain ⟨C, hC⟩ := planarBrownianMotion_blockExit_separated_superpoly hζ0 hζ1 p
  refine ⟨C, fun z s hs F K a r ha hr0 hr1 hars hK => ?_⟩
  refine le_trans (measure_mono_ae ?_)
    (hC z s hs F K a (s / 2) r ha hr0 hr1 (by linarith) hK)
  filter_upwards [ae_planarBrownianMotion_unbounded_range z] with ω hω hmem
  exact fun n hn => ⟨(half_lt_norm_blockExit_step hs hω n (hmem n hn).1).le, (hmem n hn).2⟩

end BlockExit

end MatedCRT
