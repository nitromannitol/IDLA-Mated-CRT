import MatedCRT.FirstPass.Derived.PaperCellSelectorScaling
import MatedCRT.FirstPass.Derived.ShiftedEmbeddedWalkLawDilation

/-! # Scaling of selected Brownian-edge walk laws -/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace MatedCRT

/-- The embedded Brownian-edge walk law at reciprocal floor mesh, started at
corresponding least-index cells, transforms by spatial scaling. -/
theorem interpolatedBrownianWalkLaw_reciprocal_floor_mesh_vertexOf
    {b c : ℝ} (hb : 0 < b) (hb1 : b < 1) (hc : 0 < c)
    {R : ℂ} (hR : R ≠ 0) (θ : ℝ)
    (w w' : MatedCRTHarmonic.MatedCRT.Path2)
    (hw : ∀ t, w' t =
      (c * (w (((⌊b⁻¹⌋₊ : ℝ) * b) * t)).1,
       c * (w (((⌊b⁻¹⌋₊ : ℝ) * b) * t)).2))
    (η η' : ℝ → ℂ)
    (hη : ∀ t, η' t = R⁻¹ * η (((⌊b⁻¹⌋₊ : ℝ) * b) * t))
    (speed : ℝ) (x : ℂ) :
    (srwLaw (bmEdgeCount ((⌊b⁻¹⌋₊ : ℝ)⁻¹)
        (fun t => (w' (t + ((⌊b⁻¹⌋₊ : ℝ)⁻¹) * θ)).1)
        (fun t => (w' (t + ((⌊b⁻¹⌋₊ : ℝ)⁻¹) * θ)).2))
        (vertexOf ((⌊b⁻¹⌋₊ : ℝ)⁻¹)
          (fun t => η' (t + ((⌊b⁻¹⌋₊ : ℝ)⁻¹) * θ)) x)).map
      (interpolatedWalk ((⌊b⁻¹⌋₊ : ℝ)⁻¹)
        (fun t => η' (t + ((⌊b⁻¹⌋₊ : ℝ)⁻¹) * θ)) speed) =
    ((srwLaw (bmEdgeCount b (fun t => (w (t + b * θ)).1)
        (fun t => (w (t + b * θ)).2))
        (vertexOf b (fun t => η (t + b * θ)) (R * x))).map
      (interpolatedWalk b (fun t => η (t + b * θ)) speed)).map
        (fun p t => R⁻¹ * p t) := by
  rw [vertexOf_reciprocal_floor_mesh hb hb1 hR θ η η' hη x]
  obtain ⟨hn, hmesh⟩ := LatticeProb.reciprocal_floor_mesh_eq hb hb1
  have hq : 0 < (⌊b⁻¹⌋₊ : ℝ) * b := by positivity
  rw [← hmesh]
  exact interpolatedWalkLaw_shiftedPhysical_rescale hq hc θ w w' hw R η η' hη speed _

end MatedCRT
