import MatedCRT.FirstPass.Derived.ShiftedAreaCellConfig
import MatedCRT.FirstPass.Derived.AreaCellInducedConnectivity

/-! # Induced graphs of time-shifted area cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS

/-- Shifted cell adjacency agrees with integer adjacency for symmetric multiplicities. -/
theorem shiftedAreaCellConfig_graph_adj_iff {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (θ : ℝ)
    (m : ℤ → ℤ → ℕ) (hsymm : ∀ a b, m a b = m b a) (a b : ℤ) :
    (shiftedAreaCellConfig h hε θ m).graph.Adj (shiftedEuclideanCellEquiv h hε θ a)
      (shiftedEuclideanCellEquiv h hε θ b) ↔ (srwGraph m).Adj a b := by
  change (shiftedEuclideanCellEquiv h hε θ a ≠ shiftedEuclideanCellEquiv h hε θ b ∧
    0 < (shiftedAreaCellConfig h hε θ m).c (shiftedEuclideanCellEquiv h hε θ a)
      (shiftedEuclideanCellEquiv h hε θ b) ∧
    0 < (shiftedAreaCellConfig h hε θ m).c (shiftedEuclideanCellEquiv h hε θ b)
      (shiftedEuclideanCellEquiv h hε θ a)) ↔
      (a ≠ b ∧ (m a b ≠ 0 ∨ m b a ≠ 0))
  rw [shiftedAreaCellConfig_conductance, shiftedAreaCellConfig_conductance, ← hsymm a b]
  simp only [ne_eq, (shiftedEuclideanCellEquiv h hε θ).injective.eq_iff, Nat.cast_pos,
    Nat.pos_iff_ne_zero, and_self, or_self]

/-- The integer graph is isomorphic to the graph of the shifted area cells. -/
noncomputable def shiftedAreaCellGraphIso {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (θ : ℝ)
    (m : ℤ → ℤ → ℕ) (hsymm : ∀ a b, m a b = m b a) :
    srwGraph m ≃g (shiftedAreaCellConfig h hε θ m).graph where
  toEquiv := shiftedEuclideanCellEquiv h hε θ
  map_rel_iff' := (shiftedAreaCellConfig_graph_adj_iff h hε θ m hsymm _ _)

/-- Shifted cell labels identify the induced graphs of cells meeting a target. -/
noncomputable def shiftedAreaCellInducedGraphIso {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (θ : ℝ)
    (m : ℤ → ℤ → ℕ) (hsymm : ∀ a b, m a b = m b a) (U : Set ReflectedGMS.Plane) :
    (srwGraph m).induce
      (cellVertices ε (fun t => η (t + ε * θ)) (Complex.orthonormalBasisOneI.repr ⁻¹' U)) ≃g
      (shiftedAreaCellConfig h hε θ m).inducedGraph U := by
  let e := shiftedAreaCellGraphIso h hε θ m hsymm
  have hm : ∀ a : ℤ,
      a ∈ cellVertices ε (fun t => η (t + ε * θ))
        (Complex.orthonormalBasisOneI.repr ⁻¹' U) ↔
      (((e a).1 : Set ReflectedGMS.Plane) ∩ U).Nonempty := by
    intro a
    change (cell ε (fun t => η (t + ε * θ)) a ∩
      Complex.orthonormalBasisOneI.repr ⁻¹' U).Nonempty ↔
      ((Complex.orthonormalBasisOneI.repr '' cell ε (fun t => η (t + ε * θ)) a) ∩ U).Nonempty
    constructor
    · rintro ⟨z, hz, hzU⟩
      exact ⟨_, ⟨z, hz, rfl⟩, hzU⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, hzU⟩
      exact ⟨z, hz, hzU⟩
  refine { toEquiv := e.toEquiv.subtypeEquiv hm, map_rel_iff' := ?_ }
  intro a b
  exact e.map_rel_iff

/-- Connectivity is preserved by the shifted cell labels. -/
theorem shiftedAreaCellConfig_inducedGraph_connected {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (θ : ℝ)
    (m : ℤ → ℤ → ℕ) (hsymm : ∀ a b, m a b = m b a) (U : Set ReflectedGMS.Plane)
    (hconn : ((srwGraph m).induce
      (cellVertices ε (fun t => η (t + ε * θ))
        (Complex.orthonormalBasisOneI.repr ⁻¹' U))).Connected) :
    ((shiftedAreaCellConfig h hε θ m).inducedGraph U).Connected :=
  (shiftedAreaCellInducedGraphIso h hε θ m hsymm U).connected_iff.mp hconn

end MatedCRT
