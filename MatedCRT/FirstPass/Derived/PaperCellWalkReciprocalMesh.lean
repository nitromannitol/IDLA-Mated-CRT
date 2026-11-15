import MatedCRT.FirstPass.Derived.PaperCellWalkLawDilation
import LatticeProb.Analysis.ReciprocalFloorMesh

/-! # Embedded cell walk laws at reciprocal meshes -/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace MatedCRT

/-- A positive mesh below one corresponds to the reciprocal of its floor index
under the associated time rescaling. -/
theorem interpolatedCellWalkLaw_reciprocal_floor_mesh
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) {R : ℂ} (hR : R ≠ 0)
    (θ : ℝ) (η η' : ℝ → ℂ)
    (hη : ∀ t, η' t = R⁻¹ * η (((⌊b⁻¹⌋₊ : ℝ) * b) * t))
    (speed : ℝ) (k : ℤ) :
    (srwLaw (cellMult ((⌊b⁻¹⌋₊ : ℝ)⁻¹)
        (fun t => η' (t + ((⌊b⁻¹⌋₊ : ℝ)⁻¹) * θ))) k).map
      (interpolatedWalk ((⌊b⁻¹⌋₊ : ℝ)⁻¹)
        (fun t => η' (t + ((⌊b⁻¹⌋₊ : ℝ)⁻¹) * θ)) speed) =
    ((srwLaw (cellMult b (fun t => η (t + b * θ))) k).map
      (interpolatedWalk b (fun t => η (t + b * θ)) speed)).map
        (fun p t => R⁻¹ * p t) := by
  obtain ⟨hn, hmesh⟩ := LatticeProb.reciprocal_floor_mesh_eq hb hb1
  have hq : 0 < (⌊b⁻¹⌋₊ : ℝ) * b := by positivity
  rw [← hmesh]
  exact interpolatedCellWalkLaw_shiftedPhysical_rescale hq hR θ η η' hη speed k

end MatedCRT
