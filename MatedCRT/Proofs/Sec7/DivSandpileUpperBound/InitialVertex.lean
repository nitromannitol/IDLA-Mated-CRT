import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.CellIntegral

/-! Sampling vertex values from their rescaling on each cell. -/

namespace MatedCRT.Sec7

open MeasureTheory Set Filter

/-- Every positive-mesh cell contains a point whose selected representative is
its own vertex. This lets uniform bounds on rescaled functions control every
vertex, including vertices whose cells overlap at boundary points. -/
theorem exists_vertexOf_eq_on_cell {μ : Measure ℂ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {ε : ℝ} (hε : 0 < ε) (a : ℤ) :
    ∃ x ∈ cell ε η a, vertexOf ε η x = a := by
  have hmeas : MeasurableSet (cell ε η a) :=
    (isCompact_Icc.image hη.1).isClosed.measurableSet
  let : NeBot (ae (μ.restrict (cell ε η a))) := by
    apply ae_restrict_neBot.mpr
    rw [measure_cell_of_area_parametrized hη hε]
    exact (ENNReal.ofReal_pos.mpr hε).ne'
  have h : ∀ᵐ x ∂μ.restrict (cell ε η a),
      x ∈ cell ε η a ∧ vertexOf ε η x = a := by
    filter_upwards [ae_restrict_mem hmeas, ae_vertexOf_eq_on_cell hη hp hε a] with x hx hv
    exact ⟨hx, hv⟩
  exact h.exists

/-- A uniform estimate for two rescaled vertex functions controls their
difference at each vertex whose cell lies in the estimated region. -/
theorem vertex_difference_bound_of_rescale_bound {μ : Measure ℂ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {ε : ℝ} (hε : 0 < ε) (m : ℝ) (u v : ℤ → ℝ) (K : Set ℂ)
    (C : ℝ) (a : ℤ) (hcell : cell ε η a ⊆ K)
    (hbound : ∀ x ∈ K, |rescale m ε η u x - rescale m ε η v x| ≤ C) :
    |m⁻¹ * (u a - v a)| ≤ C := by
  obtain ⟨x, hx, ha⟩ := exists_vertexOf_eq_on_cell hη hp hε a
  simpa [rescale, ha, mul_sub] using hbound x (hcell hx)

end MatedCRT.Sec7
