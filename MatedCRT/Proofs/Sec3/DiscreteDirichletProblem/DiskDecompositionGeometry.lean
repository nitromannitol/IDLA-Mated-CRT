import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ProjectedGeometry
import MatedCRT.Proofs.Sec4.SubsequentialProperties.DiscreteComparison

/-! # Finite-domain geometry for the discrete disk -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology

/-- The interior and boundary cell sets of a disk are finite; neighbouring
vertices of an interior cell lie in their union, and the walk exits the
interior almost surely. -/
theorem disk_dirichlet_decomposition_geometry
    {m : ℤ → ℤ → ℕ} {ε r : ℝ} {η : ℝ → ℂ} {z : ℂ}
    (hε : 0 < ε) (hr : 0 < r) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hadj : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hlf : IsLocallyFiniteMult m) (hsucc : ∀ k, m k (k + 1) ≠ 0) :
    (interiorCellVertices ε η (ball z r)).Finite ∧
    (cellVertices ε η (sphere z r)).Finite ∧
    (∀ a ∈ interiorCellVertices ε η (ball z r), ∀ b,
      m a b ≠ 0 → b ∈ interiorCellVertices ε η (ball z r) ∪
        cellVertices ε η (sphere z r)) ∧
    (cellVertices ε η (ball z r) ⊆ interiorCellVertices ε η (ball z r) ∪
      cellVertices ε η (sphere z r)) ∧
    (∀ a ∈ interiorCellVertices ε η (ball z r),
      ∀ᵐ x ∂srwLaw m a, vExitTime (interiorCellVertices ε η (ball z r)) x ≠ ⊤) := by
  have hA : (interiorCellVertices ε η (ball z r)).Finite :=
    (Tightness.cellVertices_finite hη hp hε isBounded_ball).subset (fun _ ha => ha.1)
  have hB : (cellVertices ε η (sphere z r)).Finite :=
    Tightness.cellVertices_finite hη hp hε isBounded_sphere
  refine ⟨hA, hB, ?_, ?_, projectedWalk_ae_finite_exit_of_finite m hlf hsucc ε η r z hA⟩
  · intro a ha b hab
    by_cases hb : b ∈ interiorCellVertices ε η (ball z r)
    · exact Or.inl hb
    · exact Or.inr (vBoundary_interiorCellVertices_subset hη hr hadj ⟨hb, a, ha, hab⟩)
  · intro a ha
    by_cases hb : a ∈ interiorCellVertices ε η (ball z r)
    · exact Or.inl hb
    · exact Or.inr (mem_cellVertices_sphere_of_not_mem_interior hr ha hb)

end MatedCRT
