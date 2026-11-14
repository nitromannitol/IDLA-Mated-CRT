import MatedCRT.FirstPass.Derived.AreaCellConfig
import MatedCRT.FirstPass.Derived.HarnackRingGeometry

/-! # Endpoint representatives of curve cells -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS

/-- The right endpoint of the time interval defining a curve cell, expressed
in Euclidean coordinates. -/
def areaCellRepresentative {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    (K : (areaCellConfig h hε m).cells) : ReflectedGMS.Plane :=
  Complex.orthonormalBasisOneI.repr (vertexPoint ε η ((euclideanCellEquiv h hε).symm K))

/-- The representative of the cell labelled by an integer is its embedded vertex. -/
theorem areaCellRepresentative_equiv {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ) (k : ℤ) :
    areaCellRepresentative h hε m (euclideanCellEquiv h hε k) =
      Complex.orthonormalBasisOneI.repr (vertexPoint ε η k) := by
  simp [areaCellRepresentative]

/-- Each endpoint representative belongs to its associated compact cell. -/
theorem areaCellRepresentative_mem {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    (K : (areaCellConfig h hε m).cells) :
    areaCellRepresentative h hε m K ∈ (K.1 : Set ReflectedGMS.Plane) := by
  obtain ⟨k, rfl⟩ := (euclideanCellEquiv h hε).surjective K
  rw [areaCellRepresentative_equiv]
  change Complex.orthonormalBasisOneI.repr (vertexPoint ε η k) ∈
    (euclideanCell ε η h.1 hε k : Set ReflectedGMS.Plane)
  rw [coe_euclideanCell]
  exact ⟨_, vertexPoint_mem_cell hε.le η k, rfl⟩

end MatedCRT
end
