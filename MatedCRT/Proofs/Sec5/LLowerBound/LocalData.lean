import MatedCRT.Proofs.Sec5.LLowerBound.SmallCells

/-!
# Local data for the Green-sum lower bound

The logarithmic Green estimate and the counting-measure estimate provide the
local sets in `LLowerBoundLocalStep` once the cell geometry is controlled.
-/

namespace MatedCRT

open MeasureTheory Set Metric

/-- Construct the local vertex sets and mass used in the Green-sum estimate. -/
theorem localData_of_geometry_and_counting {m : ℤ → ℤ → ℕ}
    {μ : Measure ℂ} {η : ℝ → ℂ} {ε δ ρ R r d C α β : ℝ} {A : Set ℤ} {a : ℤ}
    (hη : IsAreaParametrized μ η) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hβ : 0 < β) (hA : A.Finite) (ha : a ∈ A)
    (hdist : δ < infDist (vertexPoint ε η a) (frontier (fillCells ε η A)))
    (hR : R ≤ δ / 2) (hr : r ≤ R) (hgap : r + d < R) (hd : d ≤ δ / 4)
    (hC : 0 < C) (hinv : Real.exp (3 / 2 * C) ≤ ε⁻¹)
    (hscale : Real.exp (3 / 2 * C) * (r + d) ≤ R)
    (hsmall : ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) (δ / 2)),
      diam (cell ε η b) ≤ d)
    (hlog : ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) r),
      C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b then ε⁻¹
        else min (R / ‖vertexPoint ε η a - vertexPoint ε η b‖) ε⁻¹) - 1 ≤
      greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) R)) a b)
    (hball : ball (vertexPoint ε η a) r ⊆ ball 0 ρ)
    (h29 : ∀ (E : Set ℂ) (f : ℂ → ℝ) (w : ℤ → ℂ), E ⊆ ball 0 ρ →
      (∀ x ∈ thickening (ε ^ α) E, 0 ≤ f x ∧ |f x| ≤ ε ^ (-β)) →
      (∀ x ∈ thickening (ε ^ α) E, ∀ y ∈ thickening (ε ^ α) E,
        |f x - f y| ≤ ε ^ (-β) * ‖x - y‖) →
      (∀ k ∈ cellVertices ε η E, w k ∈ cell ε η k ∩ closure E) →
      ε⁻¹ * ∫ x in E, f x ∂μ - ε ^ (-1 + α) ≤ ∑' k : cellVertices ε η E, f (w k))
    (herr : ε ^ α ≤ (μ (ball (vertexPoint ε η a) r)).toReal / 2)
    (hmass : ε ^ (1 / 4 : ℝ) ≤ (μ (ball (vertexPoint ε η a) r)).toReal / 4) :
    ∃ (D Cset : Set ℤ) (α' M : ℝ), Cset.Finite ∧ D ⊆ Cset ∧ Cset ⊆ A ∧
      (∀ b ∈ D, (1 / 2 : ℝ) ≤ greenKernel m Cset a b) ∧
      ε⁻¹ * M - ε ^ (-1 + α') ≤ (D.ncard : ℝ) ∧
      ε ^ α' ≤ M / 2 ∧ ε ^ (1 / 4 : ℝ) ≤ M / 4 := by
  let D := cellVertices ε η (ball (vertexPoint ε η a) r)
  let Cset := interiorCellVertices ε η (ball (vertexPoint ε η a) R)
  have hsmallr : ∀ b ∈ D, diam (cell ε η b) ≤ d := by
    intro b hb
    obtain ⟨z, hzb, hz⟩ := hb
    exact hsmall b ⟨z, hzb, ball_subset_ball (hr.trans hR) hz⟩
  have hCA : Cset ⊆ A :=
    interiorCellVertices_subset_cluster_of_deep hη hε hδ ha hdist hR
      (fun b hb => (hsmall b hb).trans hd)
  have hDC : D ⊆ Cset := cellVertices_ball_subset_interior hη.1 hr hgap hsmallr
  have hCf := hA.subset hCA
  have hDf := hCf.subset hDC
  refine ⟨D, Cset, α, (μ (ball (vertexPoint ε η a) r)).toReal, hCf, hDC, hCA, ?_, ?_, herr, hmass⟩
  · exact greenKernel_half_of_log_on_cells hη.1 hε hC hinv hscale hsmallr hlog
  · exact count_cells_of_counting_measure hε hε1 hβ hball hDf h29

end MatedCRT
