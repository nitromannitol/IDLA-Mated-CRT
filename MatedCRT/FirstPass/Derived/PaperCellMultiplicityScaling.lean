import MatedCRT.FirstPass.Derived.ShiftedPaperCellScaling
import LatticeProb.Topology.HomeomorphComponentCount

/-! # Scaling of cell intersection multiplicities -/

set_option autoImplicit false

open Set

namespace MatedCRT

/-- A time rescaling and nonzero spatial dilation preserve cell multiplicities. -/
theorem cellMult_rescale {ε b : ℝ} {R : ℂ} (hb : 0 < b) (hR : R ≠ 0)
    (η η' : ℝ → ℂ) (hη : ∀ t, η' t = R⁻¹ * η (b * t)) (j k : ℤ) :
    cellMult (ε / b) η' j k = cellMult ε η j k := by
  classical
  by_cases h : j = k
  · simp [cellMult, h]
  · simp only [cellMult, h, ite_false]
    rw [cell_inter_rescale_image hb hR η η' hη]
    simpa only [HarmonicBalls.connectedComponentsIn, Homeomorph.coe_mulLeft₀] using
      (LatticeProb.ncard_nonsubsingleton_components_image
        (Homeomorph.mulLeft₀ R⁻¹ (inv_ne_zero hR)) (cell ε η j ∩ cell ε η k))

/-- The same multiplicity identity holds for a translated time grid. -/
theorem cellMult_shiftedPhysical_rescale {ε b : ℝ} {R : ℂ}
    (hb : 0 < b) (hR : R ≠ 0) (θ : ℝ) (η η' : ℝ → ℂ)
    (hη : ∀ t, η' t = R⁻¹ * η (b * t)) (j k : ℤ) :
    cellMult (ε / b) (fun t => η' (t + (ε / b) * θ)) j k =
      cellMult ε (fun t => η (t + ε * θ)) j k := by
  apply cellMult_rescale hb hR
  intro t
  rw [hη]
  congr 1
  congr 1
  field_simp

end MatedCRT
