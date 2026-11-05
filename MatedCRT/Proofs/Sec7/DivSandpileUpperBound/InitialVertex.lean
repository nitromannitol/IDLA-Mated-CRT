import MatedCRT.Proofs.Sec5.MeanValueInequality.CellRepresentative

/-! Sampling vertex values from their rescaling on each cell. -/

namespace MatedCRT.Sec7

open MeasureTheory Set Filter

/-- A uniform estimate for two rescaled vertex functions controls their
difference at each vertex whose cell lies in the estimated region. -/
theorem vertex_difference_bound_of_rescale_bound {μ : Measure ℂ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {ε : ℝ} (hε : 0 < ε) (m : ℝ) (u v : ℤ → ℝ) (K : Set ℂ)
    (C : ℝ) (a : ℤ) (hcell : cell ε η a ⊆ K)
    (hbound : ∀ x ∈ K, |rescale m ε η u x - rescale m ε η v x| ≤ C) :
    |m⁻¹ * (u a - v a)| ≤ C := by
  obtain ⟨x, hx, ha⟩ := exists_vertexOf_eq_of_area_parametrized hη hp hε a
  simpa [rescale, ha, mul_sub] using hbound x (hcell hx)

end MatedCRT.Sec7
