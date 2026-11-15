import MatedCRT.Proofs.Sec1.Scaling

/-! # Rescaling intersections of cells -/

namespace MatedCRT

open Set

/-- A cell of the time-rescaled curve is the inverse spatial dilation of the
corresponding original cell. -/
theorem cell_rescale_image {ε b : ℝ} {R : ℂ} (hb : 0 < b) (hR : R ≠ 0)
    (η η' : ℝ → ℂ) (hη : ∀ s, η' s = R⁻¹ * η (b * s)) (k : ℤ) :
    cell (ε / b) η' k = (fun z : ℂ => R⁻¹ * z) '' cell ε η k := by
  ext x
  constructor
  · intro hx
    exact ⟨R * x, (Sec1.mem_cell_rescale hb hR η η' hη k x).1 hx,
      inv_mul_cancel_left₀ hR x⟩
  · rintro ⟨z, hz, rfl⟩
    apply (Sec1.mem_cell_rescale hb hR η η' hη k (R⁻¹ * z)).2
    simpa only [mul_inv_cancel_left₀ hR] using hz

/-- The intersection of two rescaled cells is the inverse dilation of the
original intersection. -/
theorem cell_inter_rescale_image {ε b : ℝ} {R : ℂ} (hb : 0 < b) (hR : R ≠ 0)
    (η η' : ℝ → ℂ) (hη : ∀ s, η' s = R⁻¹ * η (b * s)) (j k : ℤ) :
    cell (ε / b) η' j ∩ cell (ε / b) η' k =
      (fun z : ℂ => R⁻¹ * z) '' (cell ε η j ∩ cell ε η k) := by
  rw [cell_rescale_image hb hR η η' hη j, cell_rescale_image hb hR η η' hη k]
  exact (Set.image_inter (mul_right_injective₀ (inv_ne_zero hR))).symm

end MatedCRT
