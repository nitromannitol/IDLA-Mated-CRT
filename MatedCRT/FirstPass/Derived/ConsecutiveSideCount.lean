import MatedCRT.FirstPass.Derived.SideCountMultiplicity
import MatedCRT.Proofs.Infra.MatingOfTrees

/-! # Side predicates for consecutive Brownian cells -/

set_option autoImplicit false

namespace MatedCRT

open Set

/-- If two side predicates match the two contour criteria, then both hold for
consecutive indices, while the Brownian graph has one edge between them. -/
theorem consecutive_side_predicates_and_edge_count
    {Ω : Type*} (A B : Ω → Prop) (ω : Ω) {ε : ℝ} (hε : 0 ≤ ε)
    {L R : ℝ → ℝ} (hL : Continuous L) (hR : Continuous R) (j : ℤ)
    (hA : A ω ↔ bmAdjacent ε L j (j + 1))
    (hB : B ω ↔ bmAdjacent ε R j (j + 1)) :
    A ω ∧ B ω ∧ bmEdgeCount ε L R j (j + 1) = 1 := by
  have ha : A ω := hA.mpr (bmAdjacent_succ hε hL j)
  have hb : B ω := hB.mpr (bmAdjacent_succ hε hR j)
  have hadj : bmAdjacent ε L j (j + 1) := bmAdjacent_succ hε hL j
  refine ⟨ha, hb, ?_⟩
  simp [bmEdgeCount, hadj]

/-- The full two-side predicate count for consecutive indices is two whenever
both predicates match their respective continuous contour criteria. -/
theorem consecutive_full_side_count
    {Ω : Type*} (A B : Ω → Prop) (ω : Ω) {ε : ℝ} (hε : 0 ≤ ε)
    {L R : ℝ → ℝ} (hL : Continuous L) (hR : Continuous R) (j : ℤ)
    (hA : A ω ↔ bmAdjacent ε L j (j + 1))
    (hB : B ω ↔ bmAdjacent ε R j (j + 1)) :
    ({ω | j ≠ j + 1 ∧ (A ω ∨ B ω)}.indicator (fun _ => (1 : ℕ))) ω +
      ({ω | j ≠ j + 1 ∧ A ω ∧ B ω}.indicator (fun _ => (1 : ℕ))) ω = 2 := by
  classical
  obtain ⟨ha, hb, _⟩ := consecutive_side_predicates_and_edge_count A B ω hε hL hR j hA hB
  simp [Set.indicator, ha, hb]

end MatedCRT
