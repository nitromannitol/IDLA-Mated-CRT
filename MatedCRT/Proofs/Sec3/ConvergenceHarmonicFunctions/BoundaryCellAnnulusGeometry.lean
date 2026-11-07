import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RestartCellInterior
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.BoundaryCellGeometry

/-! # Annuli centered at boundary-cell representatives -/

namespace MatedCRT

open Set Metric

/-- A small cell meeting a disk boundary is a valid starting cell for the
nested annuli centered at its representative and for the enlarged target
disk. The clearance is quantitative in the cell diameter. -/
theorem boundary_cell_annulus_geometry
    {ε r d cutoff : ℝ} {η : ℝ → ℂ} {z : ℂ} {a : ℤ}
    (hε : 0 ≤ ε) (hη : Continuous η) (hd : 0 < d)
    (hcut : 24 * d < cutoff)
    (hdiam : diam (cell ε η a) ≤ d)
    (ha : a ∈ cellVertices ε η (sphere z r)) :
    a ∈ interiorCellVertices ε η (ball (vertexPoint ε η a) cutoff) ∧
    a ∈ cellVertices ε η (ball (vertexPoint ε η a) (cutoff / 2)) ∧
    a ∈ interiorCellVertices ε η (ball z (r + 3 * d)) ∧
    4 * ((r + 3 * d) + d - dist (vertexPoint ε η a) z + d) < cutoff := by
  have hcut0 : 0 < cutoff := by linarith
  have hrep : vertexPoint ε η a ∈ cell ε η a := Sec7.vertexPoint_mem_cell hε a
  have hlow := boundary_cell_representative_distance_lower hε hη hdiam ha
  obtain ⟨q, hqsphere, hqnear, hsubset⟩ :=
    boundary_cell_near_and_subset_enlarged_ball hε hη (show d < 3 * d by linarith) hdiam ha
  have hstart : a ∈ interiorCellVertices ε η (ball (vertexPoint ε η a) cutoff) :=
    restart_cell_mem_interior_ball hε hη a hcut0 (by linarith)
  have htarget : a ∈ interiorCellVertices ε η (ball z (r + 3 * d)) := by
    refine ⟨⟨vertexPoint ε η a, hrep, hsubset hrep⟩, ?_⟩
    rintro ⟨w, hw, hwfront⟩
    have hwball := hsubset hw
    have hs := mem_sphere.mp (frontier_ball_subset_sphere hwfront)
    have hb := mem_ball.mp hwball
    linarith
  refine ⟨hstart, ⟨vertexPoint ε η a, hrep, mem_ball_self (by linarith)⟩, htarget, ?_⟩
  linarith

end MatedCRT

#print axioms MatedCRT.boundary_cell_annulus_geometry
