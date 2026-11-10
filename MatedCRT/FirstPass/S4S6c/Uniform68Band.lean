import MatedCRT.FirstPass.S4S6c.Uniform68Inputs
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Geometry

/-!
# The sphere-band geometry of a start vertex (q2, task fp-S4S6c-envscaling-6-7-6-8)

For a start cell `b` of the sphere band `{b | (closure (cell b) ∩ sphere c (4R/3)).Nonempty}` of the printed Lemma 6.8
(`Uniform68.config_exit_lower_bound`, `hloc`), with cell diameter bounded by `d ≤ R/100`, the vertex `η(b)` of the cell
lies in the window `‖η(b) - c‖ ∈ [4R/3 - R/100, 4R/3 + R/100]`. Consequently the test disk `B_{R/4}(η(b))` and its
`δ`-thickening, `δ ≤ R/100`, lie in the open annulus `A_{R,2R}(c)` (`OpenAnnulus68`), which are the inclusions `hDA`, `hEA`
of `Uniform68Events.hloc_point`, and the window is the hypothesis `hx` of `hF_of_goodAnnulus`.

Inputs: `hsm` is the cell-size bound `dist ≤ d` on the closure of the cell (the `hsm0` form of `CellSize68`); the vertex
lies in its cell by `ConstantOrderDiv.vertexPoint_mem_cell`.

Terminology: Duplantier-Sheffield annulus; Armitage-Gardiner test disk; LQG cell (Berestycki-Powell).
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace MatedCRT

/-- The vertex of a sphere-band cell is at distance `4R/3 ± R/100` from the centre `c`. -/
theorem vertex_band_of_cell {ε : ℝ} {η : ℝ → ℂ} {b : ℤ} {c : ℂ} {R d : ℝ} (hε : 0 ≤ ε)
    (hsm : ∀ u ∈ closure (cell ε η b), ∀ u' ∈ closure (cell ε η b), dist u u' ≤ d) (hd : d ≤ R / 100)
    (hband : (closure (cell ε η b) ∩ sphere c (4 * R / 3)).Nonempty) :
    4 * R / 3 - R / 100 ≤ ‖vertexPoint ε η b - c‖ ∧ ‖vertexPoint ε η b - c‖ ≤ 4 * R / 3 + R / 100 := by
  obtain ⟨p, hpcl, hps⟩ := hband
  have hv : vertexPoint ε η b ∈ closure (cell ε η b) :=
    subset_closure (MatedCRT.ConstantOrderDiv.vertexPoint_mem_cell hε η b)
  have hvp : dist (vertexPoint ε η b) p ≤ d := hsm _ hv _ hpcl
  have hpc : ‖p - c‖ = 4 * R / 3 := by
    rw [← dist_eq_norm]
    exact mem_sphere.1 hps
  rw [dist_eq_norm] at hvp
  have h1 := norm_sub_norm_le (vertexPoint ε η b - c) (p - c)
  rw [show (vertexPoint ε η b - c) - (p - c) = vertexPoint ε η b - p by ring] at h1
  have h2 := norm_sub_norm_le (p - c) (vertexPoint ε η b - c)
  rw [show (p - c) - (vertexPoint ε η b - c) = -(vertexPoint ε η b - p) by ring, norm_neg] at h2
  constructor <;> linarith

/-- The test disk `B_{R/4}(η(b))` and its `δ`-thickening lie in the open annulus `A_{R,2R}(c)`: the inclusions
`hDA`, `hEA` of `Uniform68Events.hloc_point`, for a sphere-band start vertex. -/
theorem disk_and_thickening_subset_of_band {ε : ℝ} {η : ℝ → ℂ} {b : ℤ} {c : ℂ} {R d δ : ℝ} (hε : 0 ≤ ε)
    (hR : 0 < R) (hsm : ∀ u ∈ closure (cell ε η b), ∀ u' ∈ closure (cell ε η b), dist u u' ≤ d)
    (hd : d ≤ R / 100) (hδ : δ ≤ R / 100)
    (hband : (closure (cell ε η b) ∩ sphere c (4 * R / 3)).Nonempty) :
    ball (vertexPoint ε η b) (R / 4) ⊆ openAnnulus c R ∧
      thickening δ (ball (vertexPoint ε η b) (R / 4)) ⊆ openAnnulus c R := by
  have hx := vertex_band_of_cell hε hsm hd hband
  exact ⟨ball_subset_openAnnulus hR hx, thickening_ball_subset_openAnnulus hR hx hδ⟩

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.vertex_band_of_cell
#print axioms MatedCRT.disk_and_thickening_subset_of_band
