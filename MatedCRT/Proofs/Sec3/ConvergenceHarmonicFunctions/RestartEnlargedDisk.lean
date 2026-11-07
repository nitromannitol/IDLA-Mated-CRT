import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RestartFiniteCircleHit
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.EnlargedBoundaryExit

/-! # Boundary restart inside the enlarged disk -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- Small cells meeting the original circle are interior cells of the disk
with radius enlarged by three cell-diameter bounds. -/
theorem boundary_cells_subset_enlarged_interior
    {ε r d : ℝ} {η : ℝ → ℂ} {z : ℂ}
    (hε : 0 ≤ ε) (hd : 0 < d) (hη : Continuous η)
    (hdiam : ∀ a ∈ cellVertices ε η (sphere z r), diam (cell ε η a) ≤ d) :
    cellVertices ε η (sphere z r) ⊆ interiorCellVertices ε η (ball z (r + 3 * d)) := by
  intro a ha
  have hsub := (boundary_cell_in_enlarged_disk hε hd hη (hdiam a ha) ha).1
  obtain ⟨q, hq, hqcircle⟩ := ha
  refine ⟨⟨q, hq, hsub hq⟩, ?_⟩
  rintro ⟨w, hw, hfront⟩
  have hin := mem_ball.mp (hsub hw)
  have hout := mem_sphere.mp (frontier_ball_subset_sphere hfront)
  linarith

/-- After the first hit of any set at a small original boundary cell, the
walk almost surely hits the boundary cells of the enlarged disk. -/
theorem srwLaw_ae_restart_enlarged_sphereCellHit_ne_top
    (m : ℤ → ℤ → ℕ) (D : Set ℤ) (a : ℤ)
    {ε r d : ℝ} {η : ℝ → ℂ} {z : ℂ}
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hε : 0 < ε) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hr : 0 < r) (hd : 0 < d)
    (hadj : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hdiam : ∀ b ∈ cellVertices ε η (sphere z r), diam (cell ε η b) ≤ d) :
    ∀ᵐ x ∂srwLaw m a, ∀ k : ℕ, vHitTime D x = k →
      x k ∈ cellVertices ε η (sphere z r) →
      vHitTime (cellVertices ε η (sphere z (r + 3 * d))) (pathShift k x) ≠ ⊤ := by
  apply srwLaw_ae_restart_sphereCellHit_ne_top m D _ a hlf hcons hε hη hp
    (show 0 < r + 3 * d by linarith) ?_ hadj
  exact boundary_cells_subset_enlarged_interior hε.le hd hη hdiam

end MatedCRT

#print axioms MatedCRT.boundary_cells_subset_enlarged_interior
#print axioms MatedCRT.srwLaw_ae_restart_enlarged_sphereCellHit_ne_top
