import MatedCRT.FirstPass.Derived.AreaCellConfigurationGeometry
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Null intersections of area-cell configurations -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic

/-- Distinct cells of a matching cellular embedding have null intersections in
Euclidean coordinates. -/
theorem areaCellConfig_volume_inter {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (hH : H.cell = cell ε η) :
    ∀ K ∈ (areaCellConfig h hε m).cells, ∀ K' ∈ (areaCellConfig h hε m).cells,
      K ≠ K' → volume ((K : Set ReflectedGMS.Plane) ∩ K') = 0 := by
  rintro K ⟨j, rfl⟩ K' ⟨k, rfl⟩ hne
  have hjk : j ≠ k := by
    intro heq
    exact hne (congrArg (euclideanCell ε η h.1 hε) heq)
  rw [coe_euclideanCell, coe_euclideanCell, ← hH,
    ← Set.image_inter Complex.orthonormalBasisOneI.repr.injective]
  change volume (Complex.orthonormalBasisOneI.repr.toLinearEquiv.toEquiv ''
    (H.cell j ∩ H.cell k)) = 0
  rw [Equiv.image_eq_preimage_symm]
  change volume (Complex.orthonormalBasisOneI.repr.symm ⁻¹'
    (H.cell j ∩ H.cell k)) = 0
  rw [Complex.orthonormalBasisOneI.measurePreserving_repr_symm.measure_preimage
    ((H.isCompact_cell j).isClosed.measurableSet.inter
      (H.isCompact_cell k).isClosed.measurableSet).nullMeasurableSet]
  exact H.volume_inter_cell j k hjk

end MatedCRT
