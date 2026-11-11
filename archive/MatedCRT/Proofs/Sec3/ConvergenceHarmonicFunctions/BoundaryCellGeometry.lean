import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.CellRadiusEvent

/-! # Boundary cell geometry for the excursion estimate -/

namespace MatedCRT

open Set Metric

/-- A cell meeting the boundary of a disk is contained in the disk enlarged
by more than its diameter. Its representative is at most one diameter from
the boundary point in that cell. -/
theorem boundary_cell_near_and_subset_enlarged_ball
    {ε r d δ : ℝ} {η : ℝ → ℂ} {z : ℂ} {a : ℤ}
    (hε : 0 ≤ ε) (hη : Continuous η) (hdδ : d < δ)
    (hdiam : Metric.diam (cell ε η a) ≤ d)
    (ha : a ∈ cellVertices ε η (sphere z r)) :
    ∃ q ∈ sphere z r, dist (vertexPoint ε η a) q ≤ d ∧
      cell ε η a ⊆ ball z (r + δ) := by
  obtain ⟨q, hqcell, hq⟩ := ha
  have hb : Bornology.IsBounded (cell ε η a) := Sec7.cell_isBounded hη a
  have hrep : vertexPoint ε η a ∈ cell ε η a := Sec7.vertexPoint_mem_cell hε a
  have hnear : dist (vertexPoint ε η a) q ≤ d :=
    (Metric.dist_le_diam_of_mem hb hrep hqcell).trans hdiam
  refine ⟨q, hq, hnear, ?_⟩
  intro w hw
  have hwq : dist w q ≤ d := (Metric.dist_le_diam_of_mem hb hw hqcell).trans hdiam
  have hqz : dist q z = r := by simpa [dist_comm] using (mem_sphere.mp hq)
  apply mem_ball.mpr
  have ht := dist_triangle w q z
  linarith

/-- A representative of a cell meeting an enlarged boundary cannot lie
much closer to the disk center than that boundary. -/
theorem boundary_cell_representative_distance_lower
    {ε r d : ℝ} {η : ℝ → ℂ} {z : ℂ} {a : ℤ}
    (hε : 0 ≤ ε) (hη : Continuous η)
    (hdiam : Metric.diam (cell ε η a) ≤ d)
    (ha : a ∈ cellVertices ε η (sphere z r)) :
    r - d ≤ dist (vertexPoint ε η a) z := by
  obtain ⟨q, hqcell, hq⟩ := ha
  have hnear := (Metric.dist_le_diam_of_mem (Sec7.cell_isBounded hη a)
    (Sec7.vertexPoint_mem_cell hε a) hqcell).trans hdiam
  have hqz : dist q z = r := by simpa [dist_comm] using (mem_sphere.mp hq)
  have ht := dist_triangle q (vertexPoint ε η a) z
  rw [dist_comm q (vertexPoint ε η a), hqz] at ht
  linarith

end MatedCRT

#print axioms MatedCRT.boundary_cell_near_and_subset_enlarged_ball
#print axioms MatedCRT.boundary_cell_representative_distance_lower
