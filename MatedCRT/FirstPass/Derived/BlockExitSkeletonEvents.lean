import MatedCRT.FirstPass.Derived.BlockExitSkeletonGoodStop

/-!
# Pointwise inclusions for the block-exit skeleton comparison of stopped paths

Deterministic ingredients of the comparison, for an open set `U`, of the walk and Brownian paths
stopped at their exit time from `U` through the block-exit skeleton. Let `s > 0`, `d' > 0` and let
`σ_N` be the `N`-th block exit time of the chain frozen on `farSet U d'`; write
`blockStopped s (farSet U d') N ω = ω ∘ min · σ_N`.

* Walk side (`stopAtExit_blockStopped_eq`, `blockStopped_mem_stopPreimage_iff`): if the chain reaches
  `farSet U d'` within `N` steps, the path stopped at `σ_N` and the path have the same stopped path
  at the exit time from `U`, so `ω` stopped at its exit time lies in `A` iff `blockStopped ω` lies
  in `{g | stopAtExit U g ∈ A}`.
* Brownian side (`exists_mem_of_cmpEDist_blockStopped_lt`): on the good event, a path `f` with
  `stopAtExit U f ∈ A` at curve distance less than `min ε d'` from `blockStopped ω` yields a member of
  `A` at curve distance less than `κ` from `ω` stopped at its exit time, for `2 ε < κ`.
* Skeleton: `blockStopped` is within `a > 8 s` of the step reconstruction of its block-exit positions
  (`cmpEDist_blockStopped_stepPath_lt`, in both orders).
-/

open MeasureTheory Set Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

open MatedCRT.StopAtExitCmp

/-- The path stopped at its `N`-th block exit time (chain frozen on `F`). -/
noncomputable def blockStopped (s : ℝ) (F : Set ℂ) (N : ℕ) (ω : ContinuousPath ℂ) : ℝ≥0 → ℂ :=
  fun t => ω (min t (blockExitTimes s F N ω))

/-- The paths that, stopped at their exit time from `U`, lie in `A`. -/
def stopPreimage (U : Set ℂ) (A : Set (ℝ≥0 → ℂ)) : Set (ℝ≥0 → ℂ) :=
  {g | stopAtExit U g ∈ A}

/-- If the chain frozen on `farSet U d'` reaches it within `N` steps, the path is in it at the `N`-th
block exit. -/
theorem blockExit_mem_farSet_of_exists {s : ℝ} {U : Set ℂ} {d' : ℝ} {N : ℕ} {ω : ContinuousPath ℂ}
    (hF : ∃ n ≤ N, ω (blockExitTimes s (farSet U d') n ω) ∈ farSet U d') :
    ω (blockExitTimes s (farSet U d') N ω) ∈ farSet U d' := by
  classical
  obtain ⟨hMN, hM⟩ : Nat.find hF ≤ N ∧
      ω (blockExitTimes s (farSet U d') (Nat.find hF) ω) ∈ farSet U d' := Nat.find_spec hF
  rw [blockExitTimes_eq_of_mem s hM N hMN]
  exact hM

/-- **Walk side.** The path stopped at the `N`-th block exit has the same stopped path at the exit
time from `U` as the path itself, once the chain has reached `farSet U d'`. -/
theorem stopAtExit_blockStopped_eq {s : ℝ} {U : Set ℂ} {d' : ℝ} (hd' : 0 < d') {N : ℕ}
    {ω : ContinuousPath ℂ} (hF : ∃ n ≤ N, ω (blockExitTimes s (farSet U d') n ω) ∈ farSet U d') :
    stopAtExit U (blockStopped s (farSet U d') N ω) = stopAtExit U ω :=
  stopAtExit_comp_min_eq ((mem_farSet.1 (blockExit_mem_farSet_of_exists hF)) _
    (by rw [dist_self]; exact hd'))

theorem blockStopped_mem_stopPreimage_iff {s : ℝ} {U : Set ℂ} {d' : ℝ} (hd' : 0 < d') {N : ℕ}
    {ω : ContinuousPath ℂ} (hF : ∃ n ≤ N, ω (blockExitTimes s (farSet U d') n ω) ∈ farSet U d')
    (A : Set (ℝ≥0 → ℂ)) :
    blockStopped s (farSet U d') N ω ∈ stopPreimage U A ↔ stopAtExit U ω ∈ A := by
  show stopAtExit U (blockStopped s (farSet U d') N ω) ∈ A ↔ _
  rw [stopAtExit_blockStopped_eq hd' hF]

/-- **Brownian side.** On the good event, if `f ∈ {g | stopAtExit U g ∈ A}` is within `r ≤ min ε d'` of
the path stopped at its `N`-th block exit, then `ω` stopped at its exit time from `U` is within `κ`
of a member of `A` (for `2 ε < κ`). -/
theorem exists_mem_of_cmpEDist_blockStopped_lt {s : ℝ} (hs : 0 < s) {U : Set ℂ} {T η : ℝ≥0}
    {d d' ε : ℝ} (hη : 0 < η) (hd' : 0 < d') (hdd : 4 * s + d' ≤ d) {N : ℕ}
    {ω : ContinuousPath ℂ} (hgood : GoodStop U T η d ε ω)
    (hF : ∃ n ≤ N, ω (blockExitTimes s (farSet U d') n ω) ∈ farSet U d') {A : Set (ℝ≥0 → ℂ)}
    {f : ℝ≥0 → ℂ} (hfA : f ∈ stopPreimage U A) {r κ : ℝ} (hr : r ≤ min ε d') (hκ : 0 < κ)
    (hεκ : 2 * ε < κ)
    (hf : cmpEDist (blockStopped s (farSet U d') N ω) f < ENNReal.ofReal r) :
    ∃ f' ∈ A, cmpEDist (stopAtExit U ω) f' < ENNReal.ofReal κ := by
  refine ⟨stopAtExit U f, hfA, ?_⟩
  have hf' : cmpEDist f (blockStopped s (farSet U d') N ω) < ENNReal.ofReal (min ε d') := by
    rw [cmpEDist_comm]
    exact lt_of_lt_of_le hf (ENNReal.ofReal_le_ofReal hr)
  have h := cmpEDist_stopAtExit_le_of_goodStop_blockExit hs hη hd' hdd hgood hF hf'
  rw [cmpEDist_comm]
  exact lt_of_le_of_lt h ((ENNReal.ofReal_lt_ofReal_iff hκ).2 hεκ)

/-- The path stopped at the `N`-th block exit is within `a > 8 s` of the step reconstruction of its
block-exit positions. -/
theorem cmpEDist_blockStopped_stepPath_lt {s : ℝ} (hs : 0 < s) {F : Set ℂ} {N : ℕ}
    {ω : ContinuousPath ℂ} (hF : ∃ n ≤ N, ω (blockExitTimes s F n ω) ∈ F) {a : ℝ} (ha : 8 * s < a) :
    cmpEDist (blockStopped s F N ω) (stepPath N (blockExitPositions s F N ω)) <
      ENNReal.ofReal a := by
  have h := cmpEDist_stoppedAtBlockExit_stepPath_le_of_exists_mem hs hF
  refine lt_of_le_of_lt h ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 ?_)
  linarith

theorem cmpEDist_stepPath_blockStopped_lt {s : ℝ} (hs : 0 < s) {F : Set ℂ} {N : ℕ}
    {ω : ContinuousPath ℂ} (hF : ∃ n ≤ N, ω (blockExitTimes s F n ω) ∈ F) {a : ℝ} (ha : 8 * s < a) :
    cmpEDist (stepPath N (blockExitPositions s F N ω)) (blockStopped s F N ω) <
      ENNReal.ofReal a := by
  rw [cmpEDist_comm]
  exact cmpEDist_blockStopped_stepPath_lt hs hF ha

end BlockExit

end MatedCRT
