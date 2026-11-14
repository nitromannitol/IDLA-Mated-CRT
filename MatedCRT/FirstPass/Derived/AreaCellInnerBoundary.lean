import MatedCRT.FirstPass.Derived.AreaCellDiameter
import MatedCRT.FirstPass.Derived.AreaCellBallTargets
import LatticeProb.Walk.CellConfigInnerBoundary

/-! # Inner boundary containment for area-parametrized curve cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Metric Set ReflectedGMS.GMS

/-- A diameter bound on the integer-labelled cells meeting a frontier puts each
corresponding Euclidean cell inside any domain containing a suitable neighborhood
of that frontier. -/
theorem areaCellConfig_subset_of_meeting_frontier {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε)
    (m : ℤ → ℤ → ℕ) (D : Set ℂ) (U : Set ReflectedGMS.Plane) {d r : ℝ}
    (hd : ∀ k ∈ cellVertices ε η (frontier D), diam (cell ε η k) ≤ d)
    (hdr : d < r)
    (hball : ∀ z ∈ frontier (Complex.orthonormalBasisOneI.repr '' D), ball z r ⊆ U)
    (K : (areaCellConfig h hε m).cells)
    (hK : ((K.1 : Set ReflectedGMS.Plane) ∩
      frontier (Complex.orthonormalBasisOneI.repr '' D)).Nonempty) :
    (K.1 : Set ReflectedGMS.Plane) ⊆ U := by
  apply LatticeProb.CellConfigBoundary.cell_subset_of_meets_frontier_of_diam_lt
    (areaCellConfig h hε m) hball K hK
  obtain ⟨k, rfl⟩ := (euclideanCellEquiv h hε).surjective K
  rw [euclideanCellEquiv_diam h hε m k]
  apply lt_of_le_of_lt (hd k ?_) hdr
  rw [← euclideanCellEquiv_preimage_meeting_frontier h hε m D]
  exact hK

end MatedCRT
