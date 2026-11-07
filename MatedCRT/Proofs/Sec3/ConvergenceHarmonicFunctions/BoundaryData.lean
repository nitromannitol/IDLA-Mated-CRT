import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ProjectedGeometry
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RetractionEstimate

/-! # Boundary data on small cells -/

namespace MatedCRT

open Filter Topology Metric Set _root_.HarmonicBalls
open scoped NNReal

/-- A cell meeting the boundary has its marked vertex in a fixed larger disk
when its radius is at most one. -/
theorem boundary_vertexPoint_mem_larger_closedBall {ε d r : ℝ} {η : ℝ → ℂ}
    {z : ℂ} (hr : 0 < r) (hd : d ≤ 1)
    (hcell : ∀ a ∈ cellVertices ε η (closedBall z r), ∀ p ∈ cell ε η a,
      dist (vertexPoint ε η a) p ≤ d)
    {a : ℤ} (ha : a ∈ cellVertices ε η (frontier (ball z r))) :
    vertexPoint ε η a ∈ closedBall z (r + 1) := by
  obtain ⟨p, hpa, hpf⟩ := ha
  have hpcl : p ∈ closedBall z r := by
    rw [← closure_ball z hr.ne']
    exact frontier_subset_closure hpf
  have hacl : a ∈ cellVertices ε η (closedBall z r) := ⟨p, hpa, hpcl⟩
  apply mem_closedBall.mpr
  have ht := dist_triangle (vertexPoint ε η a) p z
  have hpdist := mem_closedBall.mp hpcl
  linarith [hcell a hacl p hpa]

/-- The boundary Hölder constants can be chosen before the graph, mesh, and
curve, so this estimate applies uniformly on a small-cell good event. -/
theorem exists_projected_boundary_holder_constants {r : ℝ} {z : ℂ} {ψ : ℂ → ℝ}
    (hr : 0 < r) (hψ : IsHolderContinuousOn ψ (closedBall z r)) :
    ∃ C χ : ℝ≥0, 0 < χ ∧ χ ≤ 1 ∧
      ∀ (m : ℤ → ℤ → ℕ) (ε d : ℝ) (η : ℝ → ℂ), d ≤ 1 →
      (∀ a ∈ cellVertices ε η (closedBall z r), ∀ p ∈ cell ε η a,
        dist (vertexPoint ε η a) p ≤ d) →
      ∀ a ∈ cellVertices ε η (frontier (ball z r)),
      ∀ b ∈ cellVertices ε η (frontier (ball z r)),
        |projectedExitVertexValue m ε η r z ψ a - projectedExitVertexValue m ε η r z ψ b| ≤
        (C : ℝ) * max ε (dist (vertexPoint ε η a) (vertexPoint ε η b)) ^ (χ : ℝ) := by
  obtain ⟨C, χ, hχ, hχ1, hret⟩ := holder_ballRetraction hr (show 0 ≤ r + 1 by linarith) z hψ
  refine ⟨C, χ, hχ, hχ1, ?_⟩
  intro m ε d η hd hcell a ha b hb
  have haR := boundary_vertexPoint_mem_larger_closedBall hr hd hcell ha
  have hbR := boundary_vertexPoint_mem_larger_closedBall hr hd hcell hb
  simpa only [dist_eq_norm] using
    projectedExitVertexValue_boundary_holder_mesh m ε η r (r + 1) z ψ hret ha hb haR hbR

end MatedCRT
