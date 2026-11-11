import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.BoundaryCellGeometry

/-! # Uniform geometry for the GMS annulus estimate -/

namespace MatedCRT

open Set Metric

/-- One cell-size bound on a comparison disk controls the cells meeting both
relevant circles and keeps each boundary-cell representative, together with
its annulus, inside that disk. -/
theorem gms_uniform_disk_geometry
    {ε r d R ρ : ℝ} {η : ℝ → ℂ} {z : ℂ}
    (hε : 0 ≤ ε) (hη : Continuous η)
    (hd : 0 < d) (hR : 0 < R)
    (hmargin : r + 3 * d + dist z 0 + d + 2 * R < ρ)
    (hsize : ∀ i, (cell ε η i ∩ ball 0 ρ).Nonempty → diam (cell ε η i) ≤ d) :
    (∀ j ∈ interiorCellVertices ε η (ball z r) ∪ cellVertices ε η (sphere z r),
      diam (cell ε η j) ≤ d) ∧
    (∀ j ∈ cellVertices ε η (sphere z (r + 3 * d)), diam (cell ε η j) ≤ d) ∧
    (∀ j ∈ cellVertices ε η (sphere z r),
      2 * R + dist (vertexPoint ε η j) 0 ≤ ρ ∧
      vertexPoint ε η j ∈ ball 0 ρ) := by
  have hsmall : closedBall z r ⊆ ball 0 ρ :=
    closedBall_subset_ball' (by linarith)
  have hlarge : closedBall z (r + 3 * d) ⊆ ball 0 ρ :=
    closedBall_subset_ball' (by linarith)
  have hbound : ∀ j ∈ cellVertices ε η (sphere z r), diam (cell ε η j) ≤ d := by
    intro j hj
    obtain ⟨q, hqcell, hq⟩ := hj
    exact hsize j ⟨q, hqcell, hsmall (sphere_subset_closedBall hq)⟩
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    rcases hj with hj | hj
    · obtain ⟨q, hqcell, hq⟩ := hj.1
      exact hsize j ⟨q, hqcell, hsmall (ball_subset_closedBall hq)⟩
    · exact hbound j hj
  · intro j hj
    obtain ⟨q, hqcell, hq⟩ := hj
    exact hsize j ⟨q, hqcell, hlarge (sphere_subset_closedBall hq)⟩
  · intro j hj
    obtain ⟨q, hqcell, hq⟩ := hj
    have hnear := (dist_le_diam_of_mem (Sec7.cell_isBounded hη j)
      (Sec7.vertexPoint_mem_cell hε j) hqcell).trans (hbound j ⟨q, hqcell, hq⟩)
    have hqz : dist q z = r := mem_sphere.mp hq
    have hq0 := dist_triangle q z (0 : ℂ)
    have hrep0 := dist_triangle (vertexPoint ε η j) q (0 : ℂ)
    rw [hqz] at hq0
    constructor
    · linarith
    · apply mem_ball.mpr
      linarith

end MatedCRT

#print axioms MatedCRT.gms_uniform_disk_geometry
