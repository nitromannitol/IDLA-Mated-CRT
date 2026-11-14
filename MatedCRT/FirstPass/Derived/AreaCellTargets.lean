import MatedCRT.FirstPass.Derived.AreaCellConfig

/-! # Hitting targets for area-parametrized curve cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS

/-- Relabelling cells identifies Euclidean cell-intersection targets with the
integer vertices whose original complex cells meet the pulled-back set. -/
theorem euclideanCellEquiv_preimage_meeting {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε)
    (m : ℤ → ℤ → ℕ) (U : Set ReflectedGMS.Plane) :
    (euclideanCellEquiv h hε) ⁻¹'
      {K : (areaCellConfig h hε m).cells | ((K.1 : Set ReflectedGMS.Plane) ∩ U).Nonempty} =
      cellVertices ε η (Complex.orthonormalBasisOneI.repr ⁻¹' U) := by
  ext k
  change ((Complex.orthonormalBasisOneI.repr '' cell ε η k) ∩ U).Nonempty ↔
    (cell ε η k ∩ Complex.orthonormalBasisOneI.repr ⁻¹' U).Nonempty
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, hzU⟩
    exact ⟨z, hz, hzU⟩
  · rintro ⟨z, hz, hzU⟩
    exact ⟨_, ⟨z, hz, rfl⟩, hzU⟩

end MatedCRT
