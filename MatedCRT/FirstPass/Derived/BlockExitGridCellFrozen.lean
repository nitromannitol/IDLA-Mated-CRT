import MatedCRT.FirstPass.Derived.BlockExitSkeletonGoodStop
import LatticeProb.Euclidean.GridEdgeRectangle

/-!
# A frozen set made of closed grid cells, sandwiched between far sets of a ball

Fix a mesh `s > 0` and the grid `s (ℤ + i ℤ)` of `LatticeProb.GridCells`. For `ρ₀ > 0` let
`ballFrozenSet s ρ₀` be the union of the closed grid cells `[j s, (j+1) s] × [k s, (k+1) s]`
that do not meet the open disc `ball 0 ρ₀` (a staircase complement of a grid polygon).

* `GridCompatible s P`: membership in `P` is constant along each open grid edge. This is the only
  property of the rectangle `gridRectOpen` used by the kernel-continuity step of the block-exit
  chain (`mem_gridRectOpen_iff_of_le_infDist`).
* `gridCompatible_ballFrozenSet`: `ballFrozenSet s ρ₀` and its complement are grid compatible.
* `measurableSet_ballFrozenSet`: it is measurable.
* `ballFrozenSet_subset_farSet`, `farSet_subset_ballFrozenSet`: the sandwich
  `farSet (ball 0 R) d₁ ⊆ ballFrozenSet s (R + d') ⊆ farSet (ball 0 R) d'` for `d₁ ≥ d' + 2 s`.
-/

open MeasureTheory Set Metric
open LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

/-- The closed grid cell `[j s, (j+1) s] × [k s, (k+1) s]`. -/
def gridCellSet (s : ℝ) (c : ℤ × ℤ) : Set ℂ := gridRect s c.1 (c.1 + 1) c.2 (c.2 + 1)

/-- The union of the closed grid cells that do not meet the open disc `ball 0 ρ₀`. -/
def ballFrozenSet (s ρ₀ : ℝ) : Set ℂ :=
  ⋃ c ∈ {c : ℤ × ℤ | Disjoint (gridCellSet s c) (ball (0 : ℂ) ρ₀)}, gridCellSet s c

/-- Membership in `P` is constant along each open edge of the grid of mesh `s`: two grid-line points
at distance `< r ≤ s`, the first at distance at least `r` of the vertices, lie in `P` together. -/
def GridCompatible (s : ℝ) (P : Set ℂ) : Prop :=
  ∀ ⦃r : ℝ⦄, r ≤ s → ∀ ⦃y b : ℂ⦄, y ∈ gridLines s → b ∈ gridLines s → dist y b < r →
    r ≤ infDist b (vertices s) → (y ∈ P ↔ b ∈ P)

theorem GridCompatible.compl {s : ℝ} {P : Set ℂ} (h : GridCompatible s P) : GridCompatible s Pᶜ :=
  fun _ hr _ _ hy hb hd hfar => not_congr (h hr hy hb hd hfar)

theorem isClosed_gridCellSet (s : ℝ) (c : ℤ × ℤ) : IsClosed (gridCellSet s c) := by
  simp only [gridCellSet, gridRect, ofPred_and]
  exact (isClosed_le continuous_const Complex.continuous_re).inter
    ((isClosed_le Complex.continuous_re continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const)))

theorem measurableSet_ballFrozenSet (s ρ₀ : ℝ) : MeasurableSet (ballFrozenSet s ρ₀) :=
  MeasurableSet.biUnion (Set.to_countable _) fun c _ => (isClosed_gridCellSet s c).measurableSet

/-- **Grid compatibility of the union of closed cells.** -/
theorem gridCompatible_ballFrozenSet {s : ℝ} (hs : 0 < s) (ρ₀ : ℝ) :
    GridCompatible s (ballFrozenSet s ρ₀) := by
  intro r hr y b hy hb hd hfar
  simp only [ballFrozenSet, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨c, hc, hyc⟩
    exact ⟨c, hc, (mem_gridRect_iff_of_le_infDist hs hr hy hb hd hfar _ _ _ _).1 hyc⟩
  · rintro ⟨c, hc, hbc⟩
    exact ⟨c, hc, (mem_gridRect_iff_of_le_infDist hs hr hy hb hd hfar _ _ _ _).2 hbc⟩

/-- The union of the closed cells missing `ball 0 (R + d')` lies in `farSet (ball 0 R) d'`. -/
theorem ballFrozenSet_subset_farSet (s R d' : ℝ) :
    ballFrozenSet s (R + d') ⊆ farSet (ball (0 : ℂ) R) d' := by
  intro y hy
  simp only [ballFrozenSet, mem_iUnion, exists_prop, mem_ofPred_eq] at hy
  obtain ⟨c, hc, hyc⟩ := hy
  intro w hw hwR
  rw [mem_ball_zero_iff] at hwR
  have h1 : ‖y‖ ≤ ‖w‖ + ‖y - w‖ := by
    have := norm_le_insert' y w
    linarith [norm_sub_rev y w]
  have h2 : ‖y - w‖ < d' := by rwa [← dist_eq_norm, dist_comm]
  exact (Set.disjoint_left.1 hc hyc) (mem_ball_zero_iff.2 (by linarith))

/-- A far set of width `d₁ ≥ d' + 2 s` lies in the union of the closed cells missing
`ball 0 (R + d')`. -/
theorem farSet_subset_ballFrozenSet {s : ℝ} (hs : 0 < s) {R d' d₁ : ℝ} (hR : 0 < R) (hd' : 0 < d')
    (hd₁ : d' + 2 * s ≤ d₁) : farSet (ball (0 : ℂ) R) d₁ ⊆ ballFrozenSet s (R + d') := by
  intro y hy
  have hd₁0 : 0 < d₁ := by linarith
  have hyB : y ∉ ball (0 : ℂ) (R + d₁) := by
    intro h
    have h' : y ∈ thickening d₁ (ball (0 : ℂ) R) := by
      rw [thickening_ball hd₁0 hR, add_comm]
      exact h
    obtain ⟨w, hwR, hw⟩ := mem_thickening_iff.1 h'
    exact hy w (by rwa [dist_comm]) hwR
  have hyn : R + d₁ ≤ ‖y‖ := by simpa using hyB
  set c : ℤ × ℤ := (⌊y.re / s⌋, ⌊y.im / s⌋) with hc
  have hyc : y ∈ gridCellSet s c := by
    simp only [gridCellSet, gridRect, hc, mem_ofPred_eq]
    refine ⟨(le_div_iff₀ hs).1 (Int.floor_le _), ?_, (le_div_iff₀ hs).1 (Int.floor_le _), ?_⟩
    · push_cast
      exact ((div_lt_iff₀ hs).1 (Int.lt_floor_add_one _)).le
    · push_cast
      exact ((div_lt_iff₀ hs).1 (Int.lt_floor_add_one _)).le
  simp only [ballFrozenSet, mem_iUnion, exists_prop, mem_ofPred_eq]
  refine ⟨c, ?_, hyc⟩
  rw [Set.disjoint_left]
  intro q hq hqB
  have hq' : (c.1 : ℝ) * s ≤ q.re ∧ q.re ≤ (c.1 + 1 : ℤ) * s ∧ (c.2 : ℝ) * s ≤ q.im ∧
      q.im ≤ (c.2 + 1 : ℤ) * s := hq
  have hy' : (c.1 : ℝ) * s ≤ y.re ∧ y.re ≤ (c.1 + 1 : ℤ) * s ∧ (c.2 : ℝ) * s ≤ y.im ∧
      y.im ≤ (c.2 + 1 : ℤ) * s := hyc
  push_cast at hq' hy'
  have h1 : ‖q - y‖ ≤ |(q - y).re| + |(q - y).im| := Complex.norm_le_abs_re_add_abs_im _
  have h2 : |(q - y).re| ≤ s := by
    rw [Complex.sub_re, abs_le]; constructor <;> nlinarith [hq'.1, hq'.2.1, hy'.1, hy'.2.1]
  have h3 : |(q - y).im| ≤ s := by
    rw [Complex.sub_im, abs_le]
    constructor <;> nlinarith [hq'.2.2.1, hq'.2.2.2, hy'.2.2.1, hy'.2.2.2]
  have h4 : ‖y‖ ≤ ‖q‖ + ‖q - y‖ := by
    have := norm_le_insert' y q
    linarith [norm_sub_rev y q]
  have h5 : ‖q‖ < R + d' := mem_ball_zero_iff.1 hqB
  linarith

end BlockExit

end MatedCRT
