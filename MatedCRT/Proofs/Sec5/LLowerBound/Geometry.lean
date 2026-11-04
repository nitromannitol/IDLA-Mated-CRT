import MatedCRT.Proofs.Sec5.LLowerBound.GreenSum
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Model

/-!
# Geometry of the cell-union interior

A cell contained in a finite union of cells belongs to that union's vertex
set: distinct cells overlap in zero LQG mass, while each cell has positive
mass. This lets a ball inside the cell union yield a set of cluster vertices.
The cell-overlap lemma is from the Lemma 6.7 development.
-/

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal

/-- A ball centered in a set and avoiding its frontier lies in that set. -/
theorem ball_subset_of_lt_infDist_frontier {U : Set ℂ} {x : ℂ} {r : ℝ}
    (hx : x ∈ U) (hr : 0 < r) (hd : r < infDist x (frontier U)) : ball x r ⊆ U := by
  have hnot : ∀ y ∈ ball x r, y ∉ frontier U := by
    intro y hy hyF
    have h := infDist_le_dist_of_mem (x := x) hyF
    rw [mem_ball] at hy
    rw [dist_comm] at hy
    linarith
  have hxint : x ∈ interior U := (mem_interior_iff_notMem_frontier hx).2 (hnot x (mem_ball_self hr))
  have hcover : ball x r ⊆ interior U ∪ interior Uᶜ := by
    rw [← compl_frontier_eq_union_interior]
    exact fun y hy => hnot y hy
  have hdis : Disjoint (interior U) (interior Uᶜ) := by
    rw [disjoint_left]
    exact fun y hy hy' => (interior_subset hy') (interior_subset hy)
  have hnonempty : (ball x r ∩ interior U).Nonempty := ⟨x, mem_ball_self hr, hxint⟩
  exact ((convex_ball x r).isPreconnected.subset_left_of_subset_union
    isOpen_interior isOpen_interior hdis hcover hnonempty).trans interior_subset

/-- A cell contained in the union of cells indexed by `A` must itself have
index in `A`. -/
theorem mem_of_cell_subset_fillCells {μ : Measure ℂ} {η : ℝ → ℂ} {ε : ℝ}
    (hη : IsAreaParametrized μ η) (hε : 0 < ε) {A : Set ℤ} {b : ℤ}
    (hsub : cell ε η b ⊆ fillCells ε η A) : b ∈ A := by
  classical
  by_contra hb
  have hnull : μ (cell ε η b ∩ fillCells ε η A) = 0 := by
    simp only [fillCells, inter_iUnion]
    refine measure_iUnion_null fun k => measure_iUnion_null fun hk => ?_
    have hne : b ≠ k := fun h => hb (h ▸ hk)
    rcases lt_or_gt_of_ne hne with h | h
    · exact ConstantOrder.cell_inter_null hη hε h
    · rw [inter_comm]
      exact ConstantOrder.cell_inter_null hη hε h
  rw [inter_eq_left.mpr hsub] at hnull
  have hmass : μ (cell ε η b) = ENNReal.ofReal ε := by
    unfold cell
    rw [hη.2.2.2 _ _ (by nlinarith)]
    congr 1
    ring
  rw [hmass] at hnull
  exact (ENNReal.ofReal_pos.2 hε).ne' hnull

/-- A ball centered at a deep cluster vertex meets only cluster cells, if the
cells meeting the smaller ball have diameter at most one quarter of the
boundary distance. -/
theorem cellVertices_ball_subset_of_deep {μ : Measure ℂ} {η : ℝ → ℂ} {ε δ : ℝ}
    (hη : IsAreaParametrized μ η) (hε : 0 < ε) (hδ : 0 < δ) {A : Set ℤ} {a : ℤ}
    (ha : a ∈ A) (hd : δ < infDist (vertexPoint ε η a) (frontier (fillCells ε η A)))
    (hsmall : ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) (δ / 2)),
      diam (cell ε η b) ≤ δ / 4) :
    cellVertices ε η (ball (vertexPoint ε η a) (δ / 2)) ⊆ A := by
  have hxa : vertexPoint ε η a ∈ cell ε η a :=
    ⟨ε * a, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩
  have hx : vertexPoint ε η a ∈ fillCells ε η A := by
    simp only [fillCells, mem_iUnion, exists_prop]
    exact ⟨a, ha, hxa⟩
  have hball := ball_subset_of_lt_infDist_frontier hx hδ hd
  intro b hb
  apply mem_of_cell_subset_fillCells hη hε
  intro z hz
  apply hball
  have hsize := hsmall b hb
  obtain ⟨w, hwb, hw⟩ := hb
  have hdist := dist_le_diam_of_mem (isCompact_Icc.image hη.1).isBounded hz hwb
  change dist z w ≤ diam (cell ε η b) at hdist
  rw [mem_ball] at hw ⊢
  have := dist_triangle z w (vertexPoint ε η a)
  linarith

/-- If a cell meets the smaller ball and has small diameter, it does not
meet the boundary of the larger ball. -/
theorem cellVertices_ball_subset_interior {η : ℝ → ℂ} {ε R r d : ℝ} {y : ℂ}
    (hη : Continuous η) (hr : r ≤ R) (hgap : r + d < R)
    (hsmall : ∀ b ∈ cellVertices ε η (ball y r), diam (cell ε η b) ≤ d) :
    cellVertices ε η (ball y r) ⊆ interiorCellVertices ε η (ball y R) := by
  intro b hb
  have hsize := hsmall b hb
  obtain ⟨w, hwb, hw⟩ := hb
  refine ⟨⟨w, hwb, ball_subset_ball hr hw⟩, ?_⟩
  rintro ⟨z, hzb, hz⟩
  have hz' : dist z y = R := mem_sphere.1 (frontier_ball_subset_sphere hz)
  have hdist := dist_le_diam_of_mem (isCompact_Icc.image hη).isBounded hzb hwb
  change dist z w ≤ diam (cell ε η b) at hdist
  have htri := dist_triangle z w y
  rw [mem_ball] at hw
  linarith

/-- The killed walk in a sufficiently small Euclidean ball is supported on
the discrete cluster when its center is a deep cluster vertex. -/
theorem interiorCellVertices_subset_cluster_of_deep {μ : Measure ℂ} {η : ℝ → ℂ} {ε δ R : ℝ}
    (hη : IsAreaParametrized μ η) (hε : 0 < ε) (hδ : 0 < δ) {A : Set ℤ} {a : ℤ}
    (ha : a ∈ A) (hd : δ < infDist (vertexPoint ε η a) (frontier (fillCells ε η A)))
    (hR : R ≤ δ / 2)
    (hsmall : ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) (δ / 2)),
      diam (cell ε η b) ≤ δ / 4) :
    interiorCellVertices ε η (ball (vertexPoint ε η a) R) ⊆ A := by
  have hball := cellVertices_ball_subset_of_deep hη hε hδ ha hd hsmall
  intro b hb
  apply hball
  obtain ⟨z, hzb, hz⟩ := hb.1
  exact ⟨z, hzb, ball_subset_ball hR hz⟩

/-- The logarithmic Green-kernel estimate is at least `1/2` on cells meeting
a sufficiently small ball around the starting vertex. -/
theorem greenKernel_half_of_log_on_cells {m : ℤ → ℤ → ℕ} {η : ℝ → ℂ}
    {ε R r d C : ℝ} {a : ℤ} (hη : Continuous η) (hε : 0 < ε) (hC : 0 < C)
    (hinv : Real.exp (3 / 2 * C) ≤ ε⁻¹)
    (hscale : Real.exp (3 / 2 * C) * (r + d) ≤ R)
    (hsmall : ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) r),
      diam (cell ε η b) ≤ d)
    (hlog : ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) r),
      C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b then ε⁻¹
        else min (R / ‖vertexPoint ε η a - vertexPoint ε η b‖) ε⁻¹) - 1 ≤
      greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) R)) a b) :
    ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) r),
      (1 / 2 : ℝ) ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) R)) a b := by
  intro b hb
  have hbound := hlog b hb
  apply half_le_greenKernel_of_log hC _ hbound
  split_ifs with heq
  · exact hinv
  · refine le_min ?_ hinv
    have hbpoint : vertexPoint ε η b ∈ cell ε η b :=
      ⟨ε * b, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩
    have hsize := hsmall b hb
    obtain ⟨w, hwb, hw⟩ := hb
    have hdist := dist_le_diam_of_mem (isCompact_Icc.image hη).isBounded hbpoint hwb
    change dist (vertexPoint ε η b) w ≤ diam (cell ε η b) at hdist
    have htri := dist_triangle (vertexPoint ε η b) w (vertexPoint ε η a)
    rw [mem_ball] at hw
    have hnorm : ‖vertexPoint ε η a - vertexPoint ε η b‖ ≤ r + d := by
      rw [← dist_eq_norm, dist_comm]
      linarith
    have hpos : 0 < ‖vertexPoint ε η a - vertexPoint ε η b‖ :=
      norm_pos_iff.2 (sub_ne_zero.2 heq)
    apply (le_div_iff₀ hpos).2
    exact (mul_le_mul_of_nonneg_left hnorm (Real.exp_pos _).le).trans hscale

/-- The deterministic estimate at a deep cluster vertex, given the local
logarithmic Green bound and the counting-measure lower bound. -/
theorem greenSum_lower_at_deep_vertex {m : ℤ → ℤ → ℕ} {μ : Measure ℂ} {η : ℝ → ℂ}
    {ε δ R r d C α M : ℝ} {A : Set ℤ} {a : ℤ}
    (hsymm : ∀ x y, m x y = m y x) (hlf : ∀ x, {y | m x y ≠ 0}.Finite)
    (hcons : ∀ x, m x (x + 1) ≠ 0) (hA : A.Finite)
    (hη : IsAreaParametrized μ η) (hε : 0 < ε) (hδ : 0 < δ) (ha : a ∈ A)
    (hdist : δ < infDist (vertexPoint ε η a) (frontier (fillCells ε η A)))
    (hR : R ≤ δ / 2) (hr : r ≤ R) (hgap : r + d < R) (hd : d ≤ δ / 4)
    (hC : 0 < C) (hinv : Real.exp (3 / 2 * C) ≤ ε⁻¹)
    (hscale : Real.exp (3 / 2 * C) * (r + d) ≤ R)
    (hsmall : ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) (δ / 2)),
      diam (cell ε η b) ≤ d)
    (hlog : ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) r),
      C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b then ε⁻¹
        else min (R / ‖vertexPoint ε η a - vertexPoint ε η b‖) ε⁻¹) - 1 ≤
      greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) R)) a b)
    (hcount : ε⁻¹ * M - ε ^ (-1 + α) ≤
      ((cellVertices ε η (ball (vertexPoint ε η a) r)).ncard : ℝ))
    (herr : ε ^ α ≤ M / 2) (hmass : ε ^ (1 / 4 : ℝ) ≤ M / 4) :
    ε ^ (-(3 / 4 : ℝ)) ≤ ∑' b : A, greenFn m A b a := by
  have hsmallr : ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) r),
      diam (cell ε η b) ≤ d := by
    intro b hb
    obtain ⟨z, hzb, hz⟩ := hb
    exact hsmall b ⟨z, hzb, ball_subset_ball (hr.trans hR) hz⟩
  have hCA : interiorCellVertices ε η (ball (vertexPoint ε η a) R) ⊆ A :=
    interiorCellVertices_subset_cluster_of_deep hη hε hδ ha hdist hR
      (fun b hb => (hsmall b hb).trans hd)
  have hDC := cellVertices_ball_subset_interior hη.1 hr hgap hsmallr
  have hkernel := greenKernel_half_of_log_on_cells hη.1 hε hC hinv hscale hsmallr hlog
  exact greenSum_lower_of_count hsymm hlf hcons hA (hA.subset hCA) hDC hCA hε hkernel hcount herr hmass

end MatedCRT
