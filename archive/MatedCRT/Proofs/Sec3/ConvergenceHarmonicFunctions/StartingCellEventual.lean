import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.StartingCellInterior
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.PoleLocation

/-! # Eventual interior membership of the starting cell -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls

/-- For a point strictly inside a disk, the cell containing the point is an
interior vertex once the cell-size bound is small compared to the distance
to the boundary. The mesh threshold is independent of the curve. -/
theorem eventually_vertexOf_mem_interior_of_small_cells
    {a ρ r : ℝ} {z y : ℂ} (ha : 0 < a)
    (hy : y ∈ ball z r) (hball : ball z r ⊆ ball 0 ρ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ (μ : Measure ℂ) (η : ℝ → ℂ),
      IsAreaParametrized μ η → Tendsto η (cocompact ℝ) (cocompact ℂ) →
      (∀ i, (cell ε η i ∩ ball 0 ρ).Nonempty → diam (cell ε η i) ≤ ε ^ a) →
      vertexOf ε η y ∈ interiorCellVertices ε η (ball z r) := by
  have hgap : 0 < r - dist y z := by
    have h := mem_ball.mp hy
    linarith
  have hlim : Tendsto (fun ε : ℝ => ε ^ a) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : Continuous (fun ε : ℝ => ε ^ a) :=
      continuous_id.rpow_const (fun _ => Or.inr ha.le)
    simpa [Real.zero_rpow ha.ne'] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  filter_upwards [hlim (Iio_mem_nhds hgap), self_mem_nhdsWithin] with ε hsmall hε
  intro μ η hη hp hsize
  have hε0 : 0 < ε := hε
  have hycell : y ∈ cell ε η (vertexOf ε η y) :=
    Tightness.mem_cell_vertexOf hη.1 hp hη.2.2.1 hε0 y
  have hdiam := hsize (vertexOf ε η y) ⟨y, hycell, hball hy⟩
  have hsmall' : ε ^ a < r - dist y z := hsmall
  exact cell_mem_interior_ball_of_diam hη.1 hycell (by linarith)

end MatedCRT

#print axioms MatedCRT.eventually_vertexOf_mem_interior_of_small_cells
