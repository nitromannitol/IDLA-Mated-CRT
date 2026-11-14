import MatedCRT.FirstPass.Derived.AreaCellTargets

/-! # Diameters of area-parametrized cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS

/-- Euclidean coordinates preserve the diameter of each curve cell. -/
theorem euclideanCellEquiv_diam {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε)
    (m : ℤ → ℤ → ℕ) (k : ℤ) :
    Metric.diam (((euclideanCellEquiv h hε k : (areaCellConfig h hε m).cells).1 : Cell) :
      Set ReflectedGMS.Plane) = Metric.diam (cell ε η k) := by
  change Metric.diam (Complex.orthonormalBasisOneI.repr '' cell ε η k) = _
  exact Complex.orthonormalBasisOneI.repr.isometry.diam_image _

/-- A uniform diameter bound transfers to the cells meeting a Euclidean set. -/
theorem areaCellConfig_diam_le_of_meeting {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε)
    (m : ℤ → ℤ → ℕ) (U : Set ReflectedGMS.Plane) (d : ℝ)
    (hd : ∀ k ∈ cellVertices ε η (Complex.orthonormalBasisOneI.repr ⁻¹' U),
      Metric.diam (cell ε η k) ≤ d) :
    ∀ K : (areaCellConfig h hε m).cells,
      ((K.1 : Set ReflectedGMS.Plane) ∩ U).Nonempty →
        Metric.diam (K.1 : Set ReflectedGMS.Plane) ≤ d := by
  intro K hK
  obtain ⟨k, rfl⟩ := (euclideanCellEquiv h hε).surjective K
  rw [euclideanCellEquiv_diam h hε m k]
  apply hd k
  rw [← euclideanCellEquiv_preimage_meeting h hε m U]
  exact hK

end MatedCRT
