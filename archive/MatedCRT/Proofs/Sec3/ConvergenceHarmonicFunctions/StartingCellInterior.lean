import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RestartCellInterior

/-! Interior membership for a cell containing a point away from the boundary. -/

namespace MatedCRT

open Set Metric _root_.HarmonicBalls

/-- A cell containing a point in a disk is interior when its diameter is
smaller than the distance from that point to the boundary. -/
theorem cell_mem_interior_ball_of_diam
    {ε r : ℝ} {η : ℝ → ℂ} {z y : ℂ} {a : ℤ}
    (hη : Continuous η) (hy : y ∈ cell ε η a)
    (hmargin : dist y z + diam (cell ε η a) < r) :
    a ∈ interiorCellVertices ε η (ball z r) := by
  have hdiam : 0 ≤ diam (cell ε η a) := diam_nonneg
  refine ⟨⟨y, hy, mem_ball.mpr (by linarith)⟩, ?_⟩
  rintro ⟨w, hw, hfront⟩
  have hs : dist w z = r := mem_sphere.1 (frontier_ball_subset_sphere hfront)
  have hdist := dist_le_diam_of_mem (Sec7.cell_isBounded hη a) hw hy
  have htri := dist_triangle w y z
  linarith

end MatedCRT

#print axioms MatedCRT.cell_mem_interior_ball_of_diam
