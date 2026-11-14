import MatedCRT.FirstPass.Derived.AreaCellTargets

/-! # Ball and frontier targets for area-parametrized cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Metric Set ReflectedGMS.GMS

/-- Area cells meeting a transported frontier have the corresponding integer labels. -/
theorem euclideanCellEquiv_preimage_meeting_frontier {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε)
    (m : ℤ → ℤ → ℕ) (D : Set ℂ) :
    (euclideanCellEquiv h hε) ⁻¹'
      {K : (areaCellConfig h hε m).cells |
        ((K.1 : Set ReflectedGMS.Plane) ∩
          frontier (Complex.orthonormalBasisOneI.repr '' D)).Nonempty} =
      cellVertices ε η (frontier D) := by
  rw [euclideanCellEquiv_preimage_meeting]
  change cellVertices ε η (Complex.orthonormalBasisOneI.repr.toHomeomorph ⁻¹'
    frontier (Complex.orthonormalBasisOneI.repr.toHomeomorph '' D)) = _
  rw [← Complex.orthonormalBasisOneI.repr.toHomeomorph.image_frontier,
    Set.preimage_image_eq _ Complex.orthonormalBasisOneI.repr.toHomeomorph.injective]

/-- Area cells meeting a Euclidean closed ball have the labels of cells meeting
its complex-coordinate counterpart. -/
theorem euclideanCellEquiv_preimage_meeting_closedBall {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε)
    (m : ℤ → ℤ → ℕ) (z : ℂ) (r : ℝ) :
    (euclideanCellEquiv h hε) ⁻¹'
      {K : (areaCellConfig h hε m).cells |
        ((K.1 : Set ReflectedGMS.Plane) ∩
          closedBall (Complex.orthonormalBasisOneI.repr z) r).Nonempty} =
      cellVertices ε η (closedBall z r) := by
  rw [euclideanCellEquiv_preimage_meeting]
  rw [Complex.orthonormalBasisOneI.repr.isometry.preimage_closedBall]

end MatedCRT
