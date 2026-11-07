import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.BoundaryModulus
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ProjectedHarmonic

/-! # Boundary modulus for the projected harmonic extension -/

namespace MatedCRT

open Filter Topology Set Metric

/-- Boundary Hölder control and an interior vertex modulus give a modulus for
selected cell values up to the boundary. The two error terms account for the
cell radius and for the boundary-to-interior representative. -/
theorem projectedExtension_modulus_of_boundary_holder {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (r : ℝ) (z : ℂ) (ψ : ℂ → ℝ) (ε : ℝ) (ω : Ω)
    {D : Set ℂ} {d H K χ ξ : ℝ}
    (hε : 0 < ε) (hd : 0 ≤ d) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hχ : 0 ≤ χ) (hξ : 0 ≤ ξ)
    (hη : Continuous (S.η ω))
    (hp : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ))
    (hsurj : Function.Surjective (S.η ω)) (hD : IsOpen D)
    (hcell : ∀ a ∈ cellVertices ε (S.η ω) (closure D), ∀ p ∈ cell ε (S.η ω) a,
      dist (vertexPoint ε (S.η ω) a) p ≤ d)
    (hdata : ∀ a ∈ cellVertices ε (S.η ω) (frontier D),
      ∀ b ∈ cellVertices ε (S.η ω) (frontier D),
      |projectedExitVertexValue (S.mult ε ω) ε (S.η ω) r z ψ a -
        projectedExitVertexValue (S.mult ε ω) ε (S.η ω) r z ψ b| ≤
        H * max ε (dist (vertexPoint ε (S.η ω) a) (vertexPoint ε (S.η ω) b)) ^ χ)
    (hmod : ∀ a ∈ cellVertices ε (S.η ω) D, ∀ b ∈ cellVertices ε (S.η ω) D,
      |projectedExitVertexValue (S.mult ε ω) ε (S.η ω) r z ψ a -
        projectedExitVertexValue (S.mult ε ω) ε (S.η ω) r z ψ b| ≤
        K * max ε (dist (vertexPoint ε (S.η ω) a) (vertexPoint ε (S.η ω) b)) ^ ξ)
    {x y : ℂ} (hx : x ∈ closure D) (hy : y ∈ closure D)
    (hxcell : x ∈ cell ε (S.η ω) (vertexOf ε (S.η ω) x))
    (hycell : y ∈ cell ε (S.η ω) (vertexOf ε (S.η ω) y)) :
    |projectedDiscreteHarmonicExtension S r z ψ ε ω x -
      projectedDiscreteHarmonicExtension S r z ψ ε ω y| ≤
      2 * (H * max ε (2 * d) ^ χ) + K * max ε (dist x y + 6 * d) ^ ξ := by
  have ha : vertexOf ε (S.η ω) x ∈ cellVertices ε (S.η ω) (closure D) :=
    ⟨x, hxcell, hx⟩
  have hb : vertexOf ε (S.η ω) y ∈ cellVertices ε (S.η ω) (closure D) :=
    ⟨y, hycell, hy⟩
  have hxy : dist (vertexPoint ε (S.η ω) (vertexOf ε (S.η ω) x))
      (vertexPoint ε (S.η ω) (vertexOf ε (S.η ω) y)) ≤ dist x y + 2 * d := by
    have h1 := dist_triangle (vertexPoint ε (S.η ω) (vertexOf ε (S.η ω) x)) x
      (vertexPoint ε (S.η ω) (vertexOf ε (S.η ω) y))
    have h2 := dist_triangle x y (vertexPoint ε (S.η ω) (vertexOf ε (S.η ω) y))
    rw [dist_comm y] at h2
    linarith [hcell _ ha x hxcell, hcell _ hb y hycell]
  have hbound := closure_cell_modulus_of_boundary_holder hε hd hH hK hχ hξ
    hη hp hsurj hD hcell hdata hmod ha hb
  rw [projectedDiscreteHarmonicExtension_eq_vertexValue,
    projectedDiscreteHarmonicExtension_eq_vertexValue]
  have hdist : dist (vertexPoint ε (S.η ω) (vertexOf ε (S.η ω) x))
      (vertexPoint ε (S.η ω) (vertexOf ε (S.η ω) y)) + 4 * d ≤ dist x y + 6 * d := by
    linarith
  have hpow := Real.rpow_le_rpow (le_trans hε.le (le_max_left _ _))
    (max_le_max_left ε hdist) hξ
  have hk := mul_le_mul_of_nonneg_left hpow hK
  linarith

end MatedCRT
