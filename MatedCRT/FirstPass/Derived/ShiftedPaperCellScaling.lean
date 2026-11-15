import MatedCRT.FirstPass.Derived.CellIntersectionScaling

/-! # Scaling of translated paper cells -/

set_option autoImplicit false

open Set

namespace MatedCRT

/-- The cells of corresponding time-translated curves are spatial dilations
of one another. -/
theorem cell_shiftedPhysical_rescale_image {ε b : ℝ} {R : ℂ}
    (hb : 0 < b) (hR : R ≠ 0) (θ : ℝ) (η η' : ℝ → ℂ)
    (hη : ∀ t, η' t = R⁻¹ * η (b * t)) (k : ℤ) :
    cell (ε / b) (fun t => η' (t + (ε / b) * θ)) k =
      (fun z : ℂ => R⁻¹ * z) '' cell ε (fun t => η (t + ε * θ)) k := by
  apply cell_rescale_image hb hR
  intro t
  rw [hη]
  congr 1
  congr 1
  field_simp

/-- The intersection of two corresponding translated cells is the spatial
dilation of the original intersection. -/
theorem cell_inter_shiftedPhysical_rescale_image {ε b : ℝ} {R : ℂ}
    (hb : 0 < b) (hR : R ≠ 0) (θ : ℝ) (η η' : ℝ → ℂ)
    (hη : ∀ t, η' t = R⁻¹ * η (b * t)) (j k : ℤ) :
    cell (ε / b) (fun t => η' (t + (ε / b) * θ)) j ∩
        cell (ε / b) (fun t => η' (t + (ε / b) * θ)) k =
      (fun z : ℂ => R⁻¹ * z) ''
        (cell ε (fun t => η (t + ε * θ)) j ∩
          cell ε (fun t => η (t + ε * θ)) k) := by
  apply cell_inter_rescale_image hb hR
  intro t
  rw [hη]
  congr 1
  congr 1
  field_simp

end MatedCRT
