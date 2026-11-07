import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ProjectedHarmonic

/-! # Transferring a vertex modulus to the closed disk -/

namespace MatedCRT

open Metric Set

/-- A vertex estimate transfers to selected cell representatives, provided
their representatives are within `d` of their selected points. The vertex
estimate includes every cell meeting the closed disk, including boundary
cells which need not meet the open disk. Compare the compactness step in
`LEMMA36-REPLACEMENT.md`, lines 570–579. -/
theorem projectedExtension_vertex_modulus {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (r : ℝ) (z : ℂ) (ψ : ℂ → ℝ) (ε : ℝ) (ω : Ω)
    {K χ d : ℝ} (hK : 0 ≤ K) (hχ : 0 ≤ χ)
    (hcell : ∀ x ∈ closedBall z r,
      dist (vertexPoint ε (S.η ω) (vertexOf ε (S.η ω) x)) x ≤ d)
    (hmod : ∀ a ∈ cellVertices ε (S.η ω) (closedBall z r),
      ∀ b ∈ cellVertices ε (S.η ω) (closedBall z r),
      |projectedExitVertexValue (S.mult ε ω) ε (S.η ω) r z ψ a -
        projectedExitVertexValue (S.mult ε ω) ε (S.η ω) r z ψ b| ≤
        K * max ε (dist (vertexPoint ε (S.η ω) a) (vertexPoint ε (S.η ω) b)) ^ χ)
    {x y : ℂ} (hx : x ∈ closedBall z r) (hy : y ∈ closedBall z r)
    (hxcell : x ∈ cell ε (S.η ω) (vertexOf ε (S.η ω) x))
    (hycell : y ∈ cell ε (S.η ω) (vertexOf ε (S.η ω) y)) :
    |projectedDiscreteHarmonicExtension S r z ψ ε ω x -
      projectedDiscreteHarmonicExtension S r z ψ ε ω y| ≤
      K * max ε (dist x y + 2 * d) ^ χ := by
  have ha : vertexOf ε (S.η ω) x ∈ cellVertices ε (S.η ω) (closedBall z r) :=
    ⟨x, hxcell, hx⟩
  have hb : vertexOf ε (S.η ω) y ∈ cellVertices ε (S.η ω) (closedBall z r) :=
    ⟨y, hycell, hy⟩
  have hxy : dist (vertexPoint ε (S.η ω) (vertexOf ε (S.η ω) x))
      (vertexPoint ε (S.η ω) (vertexOf ε (S.η ω) y)) ≤ dist x y + 2 * d := by
    have h1 := dist_triangle (vertexPoint ε (S.η ω) (vertexOf ε (S.η ω) x)) x
      (vertexPoint ε (S.η ω) (vertexOf ε (S.η ω) y))
    have h2 := dist_triangle x y (vertexPoint ε (S.η ω) (vertexOf ε (S.η ω) y))
    rw [dist_comm y] at h2
    linarith [hcell x hx, hcell y hy]
  rw [projectedDiscreteHarmonicExtension_eq_vertexValue,
    projectedDiscreteHarmonicExtension_eq_vertexValue]
  refine (hmod _ ha _ hb).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (le_trans dist_nonneg (le_max_right _ _))
      (max_le_max_left _ hxy) hχ) hK

end MatedCRT
