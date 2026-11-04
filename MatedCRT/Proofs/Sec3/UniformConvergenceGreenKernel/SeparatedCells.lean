import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.CellAnnulus
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.EquicontinuityLemmas

/-! # Geometry of cells separated from the Green-kernel pole -/

namespace MatedCRT

open Filter Topology Set Metric MeasureTheory

/-- Interior cells of a ball are interior cells of every larger open ball. -/
theorem interiorCellVertices_ball_mono {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η)
    {z w : ℂ} {r R : ℝ} (hr : 0 < r) (hball : ball z r ⊆ ball w R) :
    interiorCellVertices ε η (ball z r) ⊆ interiorCellVertices ε η (ball w R) := by
  intro a ha
  have hcell := Tightness.cell_subset_ball hη hr ha
  constructor
  · obtain ⟨x, hx, hxr⟩ := ha.1
    exact ⟨x, hx, hball hxr⟩
  · rintro ⟨x, hx, hfront⟩
    rw [isOpen_ball.frontier_eq] at hfront
    exact hfront.2 (hball (hcell hx))

/-- If a set is separated from the pole and the cells are small, its marked
cell points remain separated from the marked point of the pole. -/
theorem separated_vertexPoints_of_small_cells
    {μ : Measure ℂ} {η : ℝ → ℂ} {ε : ℝ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hε : 0 < ε) {ρ d : ℝ} {y : ℂ} {D : Set ℂ}
    (hy : y ∈ ball 0 ρ) (hD : D ⊆ ball 0 ρ)
    (hsep : ∀ x ∈ D, 4 * d ≤ dist y x)
    (hdiam : ∀ b ∈ cellVertices ε η (ball 0 ρ),
      ∀ x ∈ cell ε η b, ∀ w ∈ cell ε η b, dist x w ≤ d) :
    ∀ b ∈ cellVertices ε η D,
      2 * d ≤ ‖vertexPoint ε η (vertexOf ε η y) - vertexPoint ε η b‖ := by
  intro b hb
  have hycell := Tightness.mem_cell_vertexOf hη.1 hp hη.2.2.1 hε y
  have hay : vertexOf ε η y ∈ cellVertices ε η (ball 0 ρ) := ⟨y, hycell, hy⟩
  obtain ⟨x, hxb, hxD⟩ := hb
  have hbρ : b ∈ cellVertices ε η (ball 0 ρ) := ⟨x, hxb, hD hxD⟩
  have h1 := hdiam _ hay y hycell _ (Tightness.vertexPoint_mem_cell hε _)
  have h2 := hdiam b hbρ _ (Tightness.vertexPoint_mem_cell hε _) x hxb
  have ht1 := dist_triangle y (vertexPoint ε η (vertexOf ε η y)) x
  have ht2 := dist_triangle (vertexPoint ε η (vertexOf ε η y)) (vertexPoint ε η b) x
  rw [← dist_eq_norm]
  linarith [hsep x hxD]

end MatedCRT
