import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.CorrectedContinuum
import MatedCRT.Proofs.Sec4.SubsequentialProperties.DirichletBoundaryComparison

/-! Projected discrete boundary values on the Euclidean circle. -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory _root_.HarmonicBalls
open scoped NNReal

/-- On the circle, projected discrete boundary data differ from the continuum
boundary data by at most the Hölder modulus at twice the cell diameter. -/
theorem abs_rescale_projected_boundary_sub_le
    {ε r M d : ℝ} {η : ℝ → ℂ} {z x : ℂ}
    (hε : 0 < ε) (hr : 0 < r) (hM : M ≠ 0) (hη : Continuous η)
    (φ : ℂ → ℝ) {C χ : ℝ≥0}
    (hφ : HolderOnWith C χ φ (closedBall z r))
    (u : ℤ → ℝ)
    (hbd : ∀ b ∈ cellVertices ε η (sphere z r),
      u b = M * φ (ballRetraction z r (vertexPoint ε η b)))
    (hx : x ∈ sphere z r) (hcell : x ∈ cell ε η (vertexOf ε η x))
    (hdiam : diam (cell ε η (vertexOf ε η x)) ≤ d) :
    |rescale M ε η u x - φ x| ≤ C * (2 * d) ^ (χ : ℝ) := by
  have hpt : dist (vertexPoint ε η (vertexOf ε η x)) x ≤ d :=
    (dist_le_diam_of_mem (isCompact_Icc.image hη).isBounded
      (Tightness.vertexPoint_mem_cell hε _) hcell).trans hdiam
  have hret := dist_ballRetraction_le hr z (vertexPoint ε η (vertexOf ε η x)) x
    (mem_closedBall.mp (sphere_subset_closedBall hx))
  rw [ballRetraction_of_mem z hr (sphere_subset_closedBall hx), div_self hr.ne'] at hret
  have hdist : dist (ballRetraction z r (vertexPoint ε η (vertexOf ε η x))) x ≤ 2 * d := by
    linarith
  have hmod := hφ.dist_le (ballRetraction_mem z hr (vertexPoint ε η (vertexOf ε η x))) (sphere_subset_closedBall hx)
  have hpow : dist (ballRetraction z r (vertexPoint ε η (vertexOf ε η x))) x ^ (χ : ℝ) ≤
      (2 * d) ^ (χ : ℝ) := Real.rpow_le_rpow dist_nonneg hdist χ.coe_nonneg
  have hb := hbd (vertexOf ε η x) ⟨x, hcell, hx⟩
  have hid : rescale M ε η u x = φ (ballRetraction z r (vertexPoint ε η (vertexOf ε η x))) := by
    simp only [rescale, hb]
    rw [← mul_assoc, inv_mul_cancel₀ hM, one_mul]
  rw [hid, ← Real.dist_eq]
  exact hmod.trans (mul_le_mul_of_nonneg_left hpow C.coe_nonneg)

end MatedCRT

#print axioms MatedCRT.abs_rescale_projected_boundary_sub_le
