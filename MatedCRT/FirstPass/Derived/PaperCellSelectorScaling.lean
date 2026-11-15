import MatedCRT.FirstPass.Derived.PaperCellWalkReciprocalMesh

/-! # Scaling of the least-index cell selector -/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace MatedCRT

/-- The least-index cell selector is preserved by time and spatial rescaling,
including the total selector's fallback when no least index exists. -/
theorem vertexOf_shiftedPhysical_rescale
    {ε q : ℝ} {R : ℂ} (hq : 0 < q) (hR : R ≠ 0) (θ : ℝ)
    (η η' : ℝ → ℂ) (hη : ∀ t, η' t = R⁻¹ * η (q * t)) (x : ℂ) :
    vertexOf (ε / q) (fun t => η' (t + (ε / q) * θ)) x =
      vertexOf ε (fun t => η (t + ε * θ)) (R * x) := by
  have hshift : ∀ t, η' (t + (ε / q) * θ) =
      R⁻¹ * η (q * t + ε * θ) := by
    intro t
    rw [hη]
    congr 1
    congr 1
    field_simp
  apply congrArg sInf
  ext k
  exact Sec1.mem_cell_rescale hq hR
    (fun t => η (t + ε * θ))
    (fun t => η' (t + (ε / q) * θ)) hshift k x

/-- Corresponding points select the same integer label at reciprocal floor mesh. -/
theorem vertexOf_reciprocal_floor_mesh
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) {R : ℂ} (hR : R ≠ 0)
    (θ : ℝ) (η η' : ℝ → ℂ)
    (hη : ∀ t, η' t = R⁻¹ * η (((⌊b⁻¹⌋₊ : ℝ) * b) * t)) (x : ℂ) :
    vertexOf ((⌊b⁻¹⌋₊ : ℝ)⁻¹)
        (fun t => η' (t + ((⌊b⁻¹⌋₊ : ℝ)⁻¹) * θ)) x =
      vertexOf b (fun t => η (t + b * θ)) (R * x) := by
  obtain ⟨hn, hmesh⟩ := LatticeProb.reciprocal_floor_mesh_eq hb hb1
  have hq : 0 < (⌊b⁻¹⌋₊ : ℝ) * b := by positivity
  rw [← hmesh]
  exact vertexOf_shiftedPhysical_rescale hq hR θ η η' hη x

/-- The reciprocal-mesh walk-law identity with the least-index cell as its start. -/
theorem interpolatedCellWalkLaw_reciprocal_floor_mesh_vertexOf
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) {R : ℂ} (hR : R ≠ 0)
    (θ : ℝ) (η η' : ℝ → ℂ)
    (hη : ∀ t, η' t = R⁻¹ * η (((⌊b⁻¹⌋₊ : ℝ) * b) * t))
    (speed : ℝ) (x : ℂ) :
    (srwLaw (cellMult ((⌊b⁻¹⌋₊ : ℝ)⁻¹)
        (fun t => η' (t + ((⌊b⁻¹⌋₊ : ℝ)⁻¹) * θ)))
        (vertexOf ((⌊b⁻¹⌋₊ : ℝ)⁻¹)
          (fun t => η' (t + ((⌊b⁻¹⌋₊ : ℝ)⁻¹) * θ)) x)).map
      (interpolatedWalk ((⌊b⁻¹⌋₊ : ℝ)⁻¹)
        (fun t => η' (t + ((⌊b⁻¹⌋₊ : ℝ)⁻¹) * θ)) speed) =
    ((srwLaw (cellMult b (fun t => η (t + b * θ)))
        (vertexOf b (fun t => η (t + b * θ)) (R * x))).map
      (interpolatedWalk b (fun t => η (t + b * θ)) speed)).map
        (fun p t => R⁻¹ * p t) := by
  rw [vertexOf_reciprocal_floor_mesh hb hb1 hR θ η η' hη x]
  exact interpolatedCellWalkLaw_reciprocal_floor_mesh hb hb1 hR θ η η' hη speed _

end MatedCRT
