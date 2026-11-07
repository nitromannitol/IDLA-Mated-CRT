import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.BoundaryData

/-! # Interior control for projected exit values -/

namespace MatedCRT

open Filter Topology Metric Set _root_.HarmonicBalls
open scoped NNReal

/-- The second estimate of discrete Hölder regularity applies to projected
exit values on a disk. Boundary control follows from retracted Hölder data and
small cells, and the supremum is bounded by the boundary datum. -/
theorem projected_interior_holder_of_discrete_holder
    (m : ℤ → ℤ → ℕ) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    {ε d r : ℝ} (hε : 0 < ε) {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {z : ℂ} (hr : 0 < r) (hd : d ≤ 1) (ψ : ℂ → ℝ)
    {B A C C' ξ' : ℝ} (hA : 0 ≤ A)
    (hψ : ∀ x ∈ closedBall z r, |ψ x| ≤ B)
    {C₀ χ : ℝ≥0} (hC₀ : (C₀ : ℝ) ≤ C')
    (hret : HolderOnWith C₀ χ (fun x => ψ (ballRetraction z r x)) (closedBall z (r + 1)))
    (hcell : ∀ a ∈ cellVertices ε η (closedBall z r), ∀ p ∈ cell ε η a,
      dist (vertexPoint ε η a) p ≤ d)
    (hregular :
      (∀ a ∈ interiorCellVertices ε η (ball z r),
        matedLaplacian m (projectedExitVertexValue m ε η r z ψ) a = 0) →
      (SimplyConnectedSpace (ball z r) ∧
        ∀ a ∈ cellVertices ε η (frontier (ball z r)),
        ∀ b ∈ cellVertices ε η (frontier (ball z r)),
          |projectedExitVertexValue m ε η r z ψ a - projectedExitVertexValue m ε η r z ψ b| ≤
          C' * max ε ‖vertexPoint ε η a - vertexPoint ε η b‖ ^ (χ : ℝ)) →
      ∀ a ∈ cellVertices ε η (ball z r), ∀ b ∈ cellVertices ε η (ball z r),
        |projectedExitVertexValue m ε η r z ψ a - projectedExitVertexValue m ε η r z ψ b| ≤
        max C (A * (⨆ v : cellVertices ε η (ball z r),
          |projectedExitVertexValue m ε η r z ψ v|)) *
          max ε ‖vertexPoint ε η a - vertexPoint ε η b‖ ^ ξ') :
    ∀ a ∈ cellVertices ε η (ball z r), ∀ b ∈ cellVertices ε η (ball z r),
      |projectedExitVertexValue m ε η r z ψ a - projectedExitVertexValue m ε η r z ψ b| ≤
      max C (A * B) * max ε ‖vertexPoint ε η a - vertexPoint ε η b‖ ^ ξ' := by
  have hharm : ∀ a ∈ interiorCellVertices ε η (ball z r),
      matedLaplacian m (projectedExitVertexValue m ε η r z ψ) a = 0 := by
    intro a ha
    exact projectedExitVertexValue_harmonic_of_proper m hlf hcons hε hη hp hr z ψ hψ ha
  have : ContractibleSpace (ball z r) := (convex_ball z r).contractibleSpace ⟨z, by simpa using hr⟩
  have hsimply : SimplyConnectedSpace (ball z r) := SimplyConnectedSpace.ofContractible _
  have hboundary : ∀ a ∈ cellVertices ε η (frontier (ball z r)),
      ∀ b ∈ cellVertices ε η (frontier (ball z r)),
      |projectedExitVertexValue m ε η r z ψ a - projectedExitVertexValue m ε η r z ψ b| ≤
        C' * max ε ‖vertexPoint ε η a - vertexPoint ε η b‖ ^ (χ : ℝ) := by
    intro a ha b hb
    have haR := boundary_vertexPoint_mem_larger_closedBall hr hd hcell ha
    have hbR := boundary_vertexPoint_mem_larger_closedBall hr hd hcell hb
    have h := projectedExitVertexValue_boundary_holder_mesh m ε η r (r + 1) z ψ hret ha hb haR hbR
    exact h.trans (mul_le_mul_of_nonneg_right hC₀ (Real.rpow_nonneg (le_max_of_le_left hε.le) _))
  intro a ha b hb
  have hs := iSup_abs_projectedExitVertexValue_le m ε η hr z ψ hψ ⟨a, ha⟩
  have hk : max C (A * (⨆ v : cellVertices ε η (ball z r),
      |projectedExitVertexValue m ε η r z ψ v|)) ≤ max C (A * B) :=
    max_le_max_left _ (mul_le_mul_of_nonneg_left hs hA)
  exact (hregular hharm ⟨hsimply, hboundary⟩ a ha b hb).trans
    (mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg (le_max_of_le_left hε.le) _))

end MatedCRT
