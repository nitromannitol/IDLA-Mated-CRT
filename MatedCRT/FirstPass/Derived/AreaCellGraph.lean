import MatedCRT.FirstPass.Derived.AreaCellConfig
import MatedCRT.FirstPass.Derived.SrwChainBridge
import MatedCRT.Proofs.Infra.MatingOfTrees

/-! # Graphs of area-parametrized curve cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ReflectedGMS.GMS

/-- For symmetric multiplicities, the cell graph has the same edges as the integer graph. -/
theorem areaCellConfig_graph_adj_iff {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    (hsymm : ∀ a b, m a b = m b a) (a b : ℤ) :
    (areaCellConfig h hε m).graph.Adj (euclideanCellEquiv h hε a)
      (euclideanCellEquiv h hε b) ↔ (srwGraph m).Adj a b := by
  change (euclideanCellEquiv h hε a ≠ euclideanCellEquiv h hε b ∧
    0 < (areaCellConfig h hε m).c (euclideanCellEquiv h hε a) (euclideanCellEquiv h hε b) ∧
    0 < (areaCellConfig h hε m).c (euclideanCellEquiv h hε b) (euclideanCellEquiv h hε a)) ↔
      (a ≠ b ∧ (m a b ≠ 0 ∨ m b a ≠ 0))
  rw [areaCellConfig_conductance, areaCellConfig_conductance, ← hsymm a b]
  simp only [ne_eq, (euclideanCellEquiv h hε).injective.eq_iff, Nat.cast_pos, Nat.pos_iff_ne_zero,
    and_self, or_self]

/-- The area-cell labels identify the integer graph with the cell graph. -/
noncomputable def areaCellGraphIso {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    (hsymm : ∀ a b, m a b = m b a) :
    srwGraph m ≃g (areaCellConfig h hε m).graph where
  toEquiv := euclideanCellEquiv h hε
  map_rel_iff' := (areaCellConfig_graph_adj_iff h hε m hsymm _ _)

/-- The mated-CRT graph is isomorphic to the graph of its area cells. -/
noncomputable def MatedCRTEnv.areaCellGraphIso {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (ω : Ω) {μ : Measure ℂ}
    (h : IsAreaParametrized μ (S.η ω)) {ε : ℝ} (hε : 0 < ε) :
    srwGraph (S.mult ε ω) ≃g (areaCellConfig h hε (S.mult ε ω)).graph :=
  MatedCRT.areaCellGraphIso h hε _ (S.mult_symm ε ω)

end MatedCRT
