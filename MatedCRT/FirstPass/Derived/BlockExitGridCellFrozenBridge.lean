import MatedCRT.FirstPass.Derived.BlockExitGridCellFrozen
import MatedCRT.FirstPass.Derived.BrownianBlockExitChain

/-!
# The union of closed grid cells missing a ball as a grid-line stable frozen set

The frozen set `F = ballFrozenSet s ρ₀` of `BlockExitGridCellFrozen` satisfies the hypotheses of the block-exit chain
frozen off a grid-line stable set (`BrownianBlockExitChain`):

* `gridLineStable_ballFrozenSet`, `gridLineStable_compl_ballFrozenSet`: `GridLineStable s` holds for
  `ballFrozenSet s ρ₀` (the frozen set `F` of the chain, with `z ∉ F` for `z` in the ball) and for its complement;
* `notMem_ballFrozenSet_of_mem_ball`: the points of `ball 0 ρ₀` are not in `ballFrozenSet s ρ₀`;
* `compl_ballFrozenSet_subset_ball`: `(ballFrozenSet s ρ₀)ᶜ ⊆ ball 0 (ρ₀ + 2 s)`, so the complement is bounded.
-/

set_option autoImplicit false

open MeasureTheory Set Metric
open LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

/-- A point lies in its grid cell. -/
theorem mem_gridCellSet_cellIndex {s : ℝ} (hs : 0 < s) (y : ℂ) : y ∈ gridCellSet s (cellIndex s y) := by
  have h1 := Int.floor_le (y.re / s)
  have h2 := Int.lt_floor_add_one (y.re / s)
  have h3 := Int.floor_le (y.im / s)
  have h4 := Int.lt_floor_add_one (y.im / s)
  rw [le_div_iff₀ hs] at h1 h3
  rw [div_lt_iff₀ hs] at h2 h4
  simp only [gridCellSet, gridRect, cellIndex, mem_ofPred_eq]
  push_cast
  exact ⟨h1, h2.le, h3, h4.le⟩

/-- Two points of one grid cell are at distance at most `2 s`. -/
theorem norm_sub_le_of_mem_gridCellSet {s : ℝ} {c : ℤ × ℤ} {y w : ℂ} (hy : y ∈ gridCellSet s c)
    (hw : w ∈ gridCellSet s c) : ‖y - w‖ ≤ 2 * s := by
  simp only [gridCellSet, gridRect, mem_ofPred_eq] at hy hw
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
  obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
  have hre : |(y - w).re| ≤ s := by
    rw [abs_le]; simp only [Complex.sub_re]; constructor <;> push_cast at hy2 hw2 <;> nlinarith
  have him : |(y - w).im| ≤ s := by
    rw [abs_le]; simp only [Complex.sub_im]; constructor <;> push_cast at hy4 hw4 <;> nlinarith
  linarith [Complex.norm_le_abs_re_add_abs_im (y - w)]

/-- The union of the closed grid cells missing a ball is grid-line stable. -/
theorem gridLineStable_ballFrozenSet {s : ℝ} (hs : 0 < s) (ρ₀ : ℝ) :
    GridLineStable s (ballFrozenSet s ρ₀) :=
  fun _ _ _ hr hy hb hd hfar => gridCompatible_ballFrozenSet hs ρ₀ hr hy hb hd hfar

/-- The complement of the union of the closed grid cells missing a ball is grid-line stable. -/
theorem gridLineStable_compl_ballFrozenSet {s : ℝ} (hs : 0 < s) (ρ₀ : ℝ) :
    GridLineStable s (ballFrozenSet s ρ₀)ᶜ :=
  fun _ _ _ hr hy hb hd hfar => (gridCompatible_ballFrozenSet hs ρ₀).compl hr hy hb hd hfar

/-- The points of the ball are not in the union of the closed grid cells missing the ball. -/
theorem notMem_ballFrozenSet_of_mem_ball {s ρ₀ : ℝ} {z : ℂ} (hz : z ∈ ball (0 : ℂ) ρ₀) :
    z ∉ ballFrozenSet s ρ₀ := by
  intro h
  simp only [ballFrozenSet, mem_iUnion, exists_prop, mem_ofPred_eq] at h
  obtain ⟨c, hc, hzc⟩ := h
  exact (Set.disjoint_left.1 hc hzc) hz

/-- The complement of the union of the closed grid cells of mesh `s` missing `ball 0 ρ₀` lies in
`ball 0 (ρ₀ + 2 s)`. -/
theorem compl_ballFrozenSet_subset_ball {s : ℝ} (hs : 0 < s) (ρ₀ : ℝ) :
    (ballFrozenSet s ρ₀)ᶜ ⊆ ball (0 : ℂ) (ρ₀ + 2 * s) := by
  intro y hy
  by_contra hyb
  apply hy
  simp only [ballFrozenSet, mem_iUnion, exists_prop, mem_ofPred_eq]
  refine ⟨cellIndex s y, ?_, mem_gridCellSet_cellIndex hs y⟩
  rw [Set.disjoint_left]
  intro w hw hwb
  have h1 := norm_sub_le_of_mem_gridCellSet (mem_gridCellSet_cellIndex hs y) hw
  rw [mem_ball_zero_iff] at hwb hyb
  have h2 : ‖y‖ ≤ ‖w‖ + ‖y - w‖ := by
    have := norm_le_insert' y w
    linarith [norm_sub_rev y w]
  linarith

end BlockExit

end MatedCRT
