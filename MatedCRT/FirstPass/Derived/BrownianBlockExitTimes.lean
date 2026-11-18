import MatedCRT.FirstPass.Derived.BrownianBlockExitPositions

/-!
# Successive block-exit times of a path

The pathwise companion of `blockExitPositions`. For a mesh `s > 0` and a frozen set `F`, the
successive block-exit times `σ₀ = 0 ≤ σ₁ ≤ σ₂ ≤ …` of a path `ω` are defined by the first-step
recursion `σ_{n+1}(ω) = σ₁(ω) + σ_n(θ_{σ₁} ω)`, where `σ₁ = firstBlockExitTime s F` and `θ` is the
time shift. The block-exit positions are the values of the path at these times, the times satisfy
the last-step recursion `σ_{n+1} = σ_n + σ₁ ∘ θ_{σ_n}`, and between two consecutive exits the path
stays in the closed block of side `3 s` around the grid cell of its position at the earlier exit.
This is the oscillation bound behind the chaining step of the proof of Theorem 3.10 of the
Gwynne-Miller-Sheffield invariance principle.

## Main results

* `blockExitTimes`, `measurable_blockExitTimes`, `monotone_blockExitTimes`.
* `blockExitPositions_apply`: `blockExitPositions s F N ω i = ω (σ_i ω)`.
* `blockExitTimes_succ'`: `σ_{n+1} ω = σ_n ω + σ₁ (θ_{σ_n ω} ω)`.
* `mem_closure_openBlock_of_le_firstBlockExitTime`: up to the first block exit the path stays in
  the closure of the open block around the cell of its starting point.
* `mem_closure_openBlock_of_blockExitTimes_le`: for `σ_n ω ≤ t ≤ σ_{n+1} ω`, the point `ω t` lies
  in the closure of the open block around the cell of `ω (σ_n ω)`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric MarkovProcess
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

/-- The successive block-exit times `σ_n` of a path, frozen once the path is in `F`, by the
first-step recursion `σ_{n+1}(ω) = σ₁(ω) + σ_n(θ_{σ₁ ω} ω)`. -/
noncomputable def blockExitTimes (s : ℝ) (F : Set ℂ) : ℕ → ContinuousPath ℂ → ℝ≥0
  | 0, _ => 0
  | n + 1, ω => firstBlockExitTime s F ω +
      blockExitTimes s F n (ContinuousPath.shift (firstBlockExitTime s F ω) ω)

theorem blockExitTimes_zero (s : ℝ) (F : Set ℂ) (ω : ContinuousPath ℂ) :
    blockExitTimes s F 0 ω = 0 :=
  rfl

theorem blockExitTimes_succ (s : ℝ) (F : Set ℂ) (n : ℕ) (ω : ContinuousPath ℂ) :
    blockExitTimes s F (n + 1) ω = firstBlockExitTime s F ω +
      blockExitTimes s F n (ContinuousPath.shift (firstBlockExitTime s F ω) ω) :=
  rfl

theorem measurable_blockExitTimes (s : ℝ) {F : Set ℂ} (hF : MeasurableSet F) (n : ℕ) :
    Measurable (blockExitTimes s F n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hsh : Measurable fun ω : ContinuousPath ℂ =>
        ContinuousPath.shift (firstBlockExitTime s F ω) ω :=
      ContinuousPath.measurable_shift_of_measurable _ (measurable_firstBlockExitTime s hF)
    exact (measurable_firstBlockExitTime s hF).add (ih.comp hsh)

/-- The block-exit positions are the values of the path at the block-exit times. -/
theorem blockExitPositions_apply (s : ℝ) (F : Set ℂ) (N : ℕ) (ω : ContinuousPath ℂ)
    (i : Fin (N + 1)) : blockExitPositions s F N ω i = ω (blockExitTimes s F i ω) := by
  induction N generalizing ω with
  | zero =>
    have hi : i = 0 := Fin.ext (Nat.lt_one_iff.1 i.isLt)
    subst hi
    rfl
  | succ N ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rw [blockExitPositions_succ, Fin.cons_succ, ih, ContinuousPath.shift_apply, Fin.val_succ,
        blockExitTimes_succ]

theorem blockExitTimes_le_succ (s : ℝ) (F : Set ℂ) :
    ∀ (n : ℕ) (ω : ContinuousPath ℂ), blockExitTimes s F n ω ≤ blockExitTimes s F (n + 1) ω
  | 0, _ => zero_le
  | n + 1, ω => by
    rw [blockExitTimes_succ s F n ω, blockExitTimes_succ s F (n + 1) ω]
    exact add_le_add_right (blockExitTimes_le_succ s F n _) _

/-- The block-exit times are nondecreasing in `n`. -/
theorem monotone_blockExitTimes (s : ℝ) (F : Set ℂ) (ω : ContinuousPath ℂ) :
    Monotone fun n => blockExitTimes s F n ω :=
  monotone_nat_of_le_succ fun n => blockExitTimes_le_succ s F n ω

/-- **Last-step recursion.** `σ_{n+1}(ω) = σ_n(ω) + σ₁(θ_{σ_n ω} ω)`. -/
theorem blockExitTimes_succ' (s : ℝ) (F : Set ℂ) :
    ∀ (n : ℕ) (ω : ContinuousPath ℂ), blockExitTimes s F (n + 1) ω =
      blockExitTimes s F n ω +
        firstBlockExitTime s F (ContinuousPath.shift (blockExitTimes s F n ω) ω)
  | 0, ω => by
    rw [blockExitTimes_succ]
    simp only [blockExitTimes_zero, ContinuousPath.shift_zero, add_zero, zero_add]
  | n + 1, ω => by
    rw [blockExitTimes_succ s F (n + 1) ω,
      blockExitTimes_succ' s F n (ContinuousPath.shift (firstBlockExitTime s F ω) ω),
      blockExitTimes_succ s F n ω, ContinuousPath.shift_add, add_assoc]

/-- The starting point lies in the open block around its own grid cell. -/
theorem mem_openBlock_cellIndex {s : ℝ} (hs : 0 < s) (y : ℂ) :
    y ∈ openBlock s (cellIndex s y).1 (cellIndex s y).2 :=
  closedBall_subset_openBlock hs (mem_closedCell_cellIndex hs y)
    (mem_closedBall_self (half_pos hs).le)

/-- Up to the first block exit, the path stays in the closure of the open block around the grid
cell of its starting point. -/
theorem mem_closure_openBlock_of_le_firstBlockExitTime {s : ℝ} (hs : 0 < s) (F : Set ℂ)
    (ω : ContinuousPath ℂ) {u : ℝ≥0} (hu : u ≤ firstBlockExitTime s F ω) :
    ω u ∈ closure (openBlock s (cellIndex s (ω 0)).1 (cellIndex s (ω 0)).2) := by
  set U := openBlock s (cellIndex s (ω 0)).1 (cellIndex s (ω 0)).2 with hUdef
  have h0 : ω 0 ∈ U := mem_openBlock_cellIndex hs (ω 0)
  have hzero : u = 0 → ω u ∈ closure U := fun h => by
    rw [h]
    exact subset_closure h0
  by_cases hF : ω 0 ∈ F
  · simp only [firstBlockExitTime, hF, ↓reduceIte, nonpos_iff_eq_zero] at hu
    exact hzero hu
  simp only [firstBlockExitTime, hF, ↓reduceIte, blockExitTimeAt,
    ContinuousPath.untopD_exitTime] at hu
  by_cases hfin : ContinuousPath.exitTime U ω = ⊤
  · rw [hfin, ENNReal.toNNReal_top, nonpos_iff_eq_zero] at hu
    exact hzero hu
  rcases hu.lt_or_eq with hlt | heq
  · have hlt' : (u : ℝ≥0∞) < ContinuousPath.exitTime U ω :=
      (ENNReal.coe_lt_coe.2 hlt).trans_eq (ENNReal.coe_toNNReal hfin)
    exact subset_closure (ContinuousPath.mem_of_lt_exitTime U ω u hlt')
  · rw [heq]
    exact frontier_subset_closure
      (ContinuousPath.coordinate_exitTime_mem_frontier U (isOpen_openBlock s _ _) ω h0 hfin)

/-- **Oscillation between consecutive block exits.** For `σ_n ω ≤ t ≤ σ_{n+1} ω`, the point
`ω t` lies in the closure of the open block of side `3 s` around the grid cell of `ω (σ_n ω)`. -/
theorem mem_closure_openBlock_of_blockExitTimes_le {s : ℝ} (hs : 0 < s) (F : Set ℂ) (n : ℕ)
    (ω : ContinuousPath ℂ) {t : ℝ≥0} (h1 : blockExitTimes s F n ω ≤ t)
    (h2 : t ≤ blockExitTimes s F (n + 1) ω) :
    ω t ∈ closure (openBlock s (cellIndex s (ω (blockExitTimes s F n ω))).1
      (cellIndex s (ω (blockExitTimes s F n ω))).2) := by
  have hu : t - blockExitTimes s F n ω ≤
      firstBlockExitTime s F (ContinuousPath.shift (blockExitTimes s F n ω) ω) :=
    tsub_le_iff_left.2 (h2.trans_eq (blockExitTimes_succ' s F n ω))
  have h := mem_closure_openBlock_of_le_firstBlockExitTime hs F
    (ContinuousPath.shift (blockExitTimes s F n ω) ω) hu
  rwa [ContinuousPath.shift_apply, ContinuousPath.shift_apply, add_zero,
    add_tsub_cancel_of_le h1] at h

end BlockExit

end MatedCRT
