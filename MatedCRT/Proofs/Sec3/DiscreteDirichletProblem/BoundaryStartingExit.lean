import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.DiskDecompositionGeometry
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Walk

/-! # Boundary-starting walks in a discrete Dirichlet domain -/

namespace MatedCRT

open Set Metric MeasureTheory

/-- A walk started outside a domain exits at its starting vertex. -/
theorem ae_vExitPosition_eq_start_of_not_mem
    {m : ℤ → ℤ → ℕ} {A : Set ℤ} {a : ℤ} (ha : a ∉ A) :
    ∀ᵐ x ∂srwLaw m a, vExitPosition A x = a := by
  filter_upwards [srwLaw_ae_start m a] with x hx
  unfold vExitPosition
  rw [vExitTime_eq_zero_of_not_mem (by rw [hx]; exact ha)]
  simp [hx]

/-- An interior exit-location estimate extends to every start in the union of
the interior and boundary, including possible overlaps. -/
theorem ae_vExitPosition_mem_of_interior_or_boundary
    {m : ℤ → ℤ → ℕ} {A B : Set ℤ}
    (hinterior : ∀ a ∈ A, ∀ᵐ x ∂srwLaw m a, vExitPosition A x ∈ B)
    {a : ℤ} (ha : a ∈ A ∪ B) :
    ∀ᵐ x ∂srwLaw m a, vExitPosition A x ∈ B := by
  by_cases hA : a ∈ A
  · exact hinterior a hA
  · have hB : a ∈ B := ha.resolve_left hA
    filter_upwards [ae_vExitPosition_eq_start_of_not_mem (m := m) hA] with x hx
    rwa [hx]

/-- For starts in cells meeting a disk, it suffices to prove the exit-location
estimate for interior cells. -/
theorem ae_vExitPosition_mem_sphere_of_interior
    {m : ℤ → ℤ → ℕ} {ε r : ℝ} {η : ℝ → ℂ} {z : ℂ} (hr : 0 < r)
    (hinterior : ∀ a ∈ interiorCellVertices ε η (ball z r),
      ∀ᵐ x ∂srwLaw m a,
        vExitPosition (interiorCellVertices ε η (ball z r)) x ∈
          cellVertices ε η (sphere z r))
    {a : ℤ} (ha : a ∈ cellVertices ε η (ball z r)) :
    ∀ᵐ x ∂srwLaw m a, vExitPosition (interiorCellVertices ε η (ball z r)) x ∈
      cellVertices ε η (sphere z r) := by
  apply ae_vExitPosition_mem_of_interior_or_boundary hinterior
  by_cases hA : a ∈ interiorCellVertices ε η (ball z r)
  · exact Or.inl hA
  · exact Or.inr (mem_cellVertices_sphere_of_not_mem_interior hr ha hA)

end MatedCRT
