import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.CellIntegral
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.Geometry

/-!
# Geometry of the truncated cell union

For the truncated Green sum, include cells in the interior of the outer ball
which do not meet the pole ball. Small cell diameter places their union between
two explicit punctured balls. Its discrepancy from the fixed punctured ball is
therefore confined to boundary shells.
-/

namespace MatedCRT

open Set Metric MeasureTheory
open scoped ENNReal

/-- The cell union used by the truncated Green sum lies in the punctured
outer ball. -/
theorem fill_truncated_cells_subset {η : ℝ → ℂ} {ε r δ : ℝ} {z y : ℂ}
    (hη : Continuous η) :
    fillCells ε η (interiorCellVertices ε η (ball z r) \ cellVertices ε η (ball y δ)) ⊆
      ball z r \ ball y δ := by
  intro x hx
  obtain ⟨a, ha, hxa⟩ := mem_iUnion.1 hx |>.imp fun _ h => mem_iUnion.1 h
  refine ⟨Sec7.interior_cell_subset_ball hη ha.1 hxa, ?_⟩
  intro hxy
  exact ha.2 ⟨x, hxa, hxy⟩

/-- Points separated from both boundaries by more than the cell diameter
belong to the truncated cell union. -/
theorem punctured_ball_subset_fill_truncated_cells {η : ℝ → ℂ} {ε r δ d : ℝ} {z y : ℂ}
    (hη : Continuous η) (hsurj : Function.Surjective η) (hε : 0 < ε) (hd : 0 ≤ d)
    (hsmall : ∀ a ∈ cellVertices ε η (ball z r), diam (cell ε η a) ≤ d) :
    ball z (r - d) \ closedBall y (δ + d) ⊆
      fillCells ε η (interiorCellVertices ε η (ball z r) \ cellVertices ε η (ball y δ)) := by
  intro x hx
  have hxr : x ∈ ball z r := ball_subset_ball (sub_le_self r hd) hx.1
  obtain ⟨t, ht⟩ := hsurj x
  let a : ℤ := ⌈t / ε⌉
  have hxa : x ∈ cell ε η a := by
    rw [← ht]
    exact Tightness.mem_cell_ceil hε t
  have ha : a ∈ cellVertices ε η (ball z r) := ⟨x, hxa, hxr⟩
  have hdist : ∀ w ∈ cell ε η a, dist w x ≤ d := by
    intro w hw
    exact (dist_le_diam_of_mem (isCompact_Icc.image hη).isBounded hw hxa).trans (hsmall a ha)
  have hsub : cell ε η a ⊆ ball z r := by
    intro w hw
    have h := dist_triangle w x z
    have hbound := hdist w hw
    have hxbound := hx.1
    rw [mem_ball] at hxbound ⊢
    linarith
  have haf : a ∉ cellVertices ε η (frontier (ball z r)) := by
    rintro ⟨w, hw, hwf⟩
    exact (disjoint_left.1 ((disjoint_frontier_iff_isOpen.2 isOpen_ball).symm)) (hsub hw) hwf
  have hay : a ∉ cellVertices ε η (ball y δ) := by
    rintro ⟨w, hw, hwy⟩
    have h := dist_triangle x w y
    have hbound := hdist w hw
    have hxout := hx.2
    rw [mem_closedBall, not_le] at hxout
    rw [mem_ball] at hwy
    rw [dist_comm x w] at h
    linarith
  exact mem_iUnion.2 ⟨a, mem_iUnion.2 ⟨⟨⟨ha, haf⟩, hay⟩, hxa⟩⟩

/-- The only points of the punctured ball omitted by the truncated cell
union lie in an outer boundary shell or an inner boundary shell. -/
theorem punctured_ball_sdiff_fill_subset_shells {η : ℝ → ℂ} {ε r δ d : ℝ} {z y : ℂ}
    (hη : Continuous η) (hsurj : Function.Surjective η) (hε : 0 < ε) (hd : 0 ≤ d)
    (hsmall : ∀ a ∈ cellVertices ε η (ball z r), diam (cell ε η a) ≤ d) :
    (ball z r \ ball y δ) \
      fillCells ε η (interiorCellVertices ε η (ball z r) \ cellVertices ε η (ball y δ)) ⊆
    (ball z r \ ball z (r - d)) ∪ (closedBall y (δ + d) \ ball y δ) := by
  intro x hx
  by_cases hinner : x ∈ ball z (r - d)
  · right
    refine ⟨?_, hx.1.2⟩
    by_contra hfar
    exact hx.2 (punctured_ball_subset_fill_truncated_cells hη hsurj hε hd hsmall ⟨hinner, hfar⟩)
  · exact Or.inl ⟨hx.1.1, hinner⟩

/-- An area-parametrized space-filling curve gives no mass to a point. -/
theorem measure_singleton_of_area_parametrized {μ : Measure ℂ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (x : ℂ) : μ {x} = 0 := by
  have hsmall : ∀ d : ℝ, 0 < d → μ {x} ≤ ENNReal.ofReal d := by
    intro d hd
    obtain ⟨t, ht⟩ := hη.2.2.1 x
    have hsub : {x} ⊆ η '' Icc (t - d / 2) (t + d / 2) := by
      intro w hw
      have h := mem_singleton_iff.1 hw
      subst w
      exact ⟨t, ⟨by linarith, by linarith⟩, ht⟩
    calc
      μ {x} ≤ μ (η '' Icc (t - d / 2) (t + d / 2)) := measure_mono hsub
      _ = ENNReal.ofReal ((t + d / 2) - (t - d / 2)) := hη.2.2.2 _ _ (by linarith)
      _ = ENNReal.ofReal d := by congr 1; ring
  apply le_antisymm _ zero_le
  refine ENNReal.le_of_forall_pos_le_add fun e he _ => ?_
  simpa using hsmall (e : ℝ) he

end MatedCRT
