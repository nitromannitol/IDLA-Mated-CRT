import MatedCRT.FirstPass.Derived.AreaCellGraph
import MatedCRT.FirstPass.Derived.AreaCellTargets

/-! # Connectivity of induced area-cell graphs -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS

/-- Integer labels identify the induced graph on cells meeting a Euclidean set. -/
noncomputable def areaCellInducedGraphIso {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    (hsymm : ∀ a b, m a b = m b a) (U : Set ReflectedGMS.Plane) :
    (srwGraph m).induce (cellVertices ε η (Complex.orthonormalBasisOneI.repr ⁻¹' U)) ≃g
      (areaCellConfig h hε m).inducedGraph U := by
  let e := areaCellGraphIso h hε m hsymm
  have hm : ∀ a : ℤ,
      a ∈ cellVertices ε η (Complex.orthonormalBasisOneI.repr ⁻¹' U) ↔
      (((e a).1 : Set ReflectedGMS.Plane) ∩ U).Nonempty := by
    intro a
    have he := euclideanCellEquiv_preimage_meeting h hε m U
    exact (Set.ext_iff.mp he a).symm
  refine { toEquiv := e.toEquiv.subtypeEquiv hm, map_rel_iff' := ?_ }
  intro a b
  exact e.map_rel_iff

/-- Connectivity is preserved when integer-labeled cells are viewed in Euclidean coordinates. -/
theorem areaCellConfig_inducedGraph_connected {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    (hsymm : ∀ a b, m a b = m b a) (U : Set ReflectedGMS.Plane)
    (hconn : ((srwGraph m).induce
      (cellVertices ε η (Complex.orthonormalBasisOneI.repr ⁻¹' U))).Connected) :
    ((areaCellConfig h hε m).inducedGraph U).Connected :=
  (areaCellInducedGraphIso h hε m hsymm U).connected_iff.mp hconn

end MatedCRT
