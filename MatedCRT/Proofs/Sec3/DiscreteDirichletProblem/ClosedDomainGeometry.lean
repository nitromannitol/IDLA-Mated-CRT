import MatedCRT.Proofs.Sec4.SubsequentialProperties.DiscreteComparison

/-! # Vertices meeting a closed disk -/

namespace MatedCRT

open Set Metric

/-- Every cell meeting a closed disk either belongs to the interior vertex
set or meets the boundary sphere. -/
theorem cellVertices_closedBall_subset_interior_union_sphere
    {ε r : ℝ} {η : ℝ → ℂ} {z : ℂ} (hr : 0 < r) :
    cellVertices ε η (closedBall z r) ⊆
      interiorCellVertices ε η (ball z r) ∪ cellVertices ε η (sphere z r) := by
  intro a ha
  by_cases hi : a ∈ interiorCellVertices ε η (ball z r)
  · exact Or.inl hi
  · right
    by_cases hb : a ∈ cellVertices ε η (ball z r)
    · exact mem_cellVertices_sphere_of_not_mem_interior hr hb hi
    · obtain ⟨x, hxcell, hxball⟩ := ha
      have hxnot : x ∉ ball z r := fun hx => hb ⟨x, hxcell, hx⟩
      refine ⟨x, hxcell, ?_⟩
      simp only [mem_ball, mem_closedBall, mem_sphere] at *
      exact le_antisymm hxball (le_of_not_gt hxnot)

end MatedCRT
