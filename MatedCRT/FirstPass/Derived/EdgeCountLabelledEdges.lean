import MatedCRT.FirstPass.Derived.MatedCRTGraphBridge
import MatedCRT.FirstPass.Derived.DegreeBoundDarts

/-!
# The edge multiplicity of the mated-CRT map counts labelled edges

Definition 1.1 gives the `γ`-mated-CRT map with cell size `ε` as the edge multiplicity
`bmEdgeCount ε L R` on `ℤ` (`MatedCRTEnv.mult`). Gwynne–Miller–Sheffield (2019), (1.1), describe
the same graph by labelled edges `(x, y, side)` with `x < y`
(`MatedCRTHarmonic.MatedCRT.IsEdge`): consecutive vertices carry the single edge
`(x, x + 1, false)`, and a non-consecutive pair carries its edge of side `L` (`false`) or `R`
(`true`) iff condition (1.1) holds for that coordinate. This file proves that the two counts agree
for every pair of distinct vertices.

## Main statements

* `MatedCRT.isEdge_iff_bmAdjacent`: for `x + 1 < y`, the labelled edge `(x, y, side)` is present
  iff the adjacency condition (eq:edge-map) holds for the coordinate of that side;
* `MatedCRT.bmEdgeCount_eq_card_isEdge`: for `ε ≥ 0` and `x < y`, `bmEdgeCount` is the number of
  labelled edges `(x, y, side)`;
* `MatedCRT.MatedCRTEnv.mult_eq_nat_card_isEdge`: the same for the map `S.mult ε ω` of an
  environment, with the count written as `Nat.card` of the set of sides.
-/

namespace MatedCRT

open Set

/-- For non-consecutive vertices `x + 1 < y`, the labelled edge `(x, y, side)` of
Gwynne–Miller–Sheffield (2019), (1.1), is present iff the adjacency condition (eq:edge-map) of
Definition 1.1 holds for the coordinate of that side (`L` for `false`, `R` for `true`). -/
theorem isEdge_iff_bmAdjacent (ε : ℝ) (ω : MatedCRTHarmonic.MatedCRT.Path2) {x y : ℤ}
    (hxy : x + 1 < y) (b : Bool) :
    MatedCRTHarmonic.MatedCRT.IsEdge ε ω (x, y, b) ↔
      bmAdjacent ε (fun t => if b then (ω t).2 else (ω t).1) x y := by
  have h1 : x < y := by omega
  have h2 : y ≠ x + 1 := by omega
  simp only [MatedCRTHarmonic.MatedCRT.IsEdge, ← bmAdjacent_iff_sideCond, h1, h2, true_and,
    false_and, false_or, ne_eq, not_false_eq_true]

open Classical in
/-- For `ε ≥ 0` and vertices `x < y`, the multiplicity `bmEdgeCount` of the mated-CRT map
(Definition 1.1) for the pair of paths `(L, R) = ω` is the number of labelled edges
`(x, y, side)` of Gwynne–Miller–Sheffield (2019), (1.1). For consecutive vertices both counts
are `1` (the paths are continuous); otherwise both count the coordinates satisfying the
adjacency condition. -/
theorem bmEdgeCount_eq_card_isEdge {ε : ℝ} (hε : 0 ≤ ε) (ω : MatedCRTHarmonic.MatedCRT.Path2)
    {x y : ℤ} (hxy : x < y) :
    bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) x y =
      (Finset.univ.filter fun s : Bool => MatedCRTHarmonic.MatedCRT.IsEdge ε ω (x, y, s)).card := by
  have hne : x ≠ y := hxy.ne
  have hmin : min x y = x := min_eq_left hxy.le
  have hmax : max x y = y := max_eq_right hxy.le
  rw [Finset.card_filter, Fintype.sum_bool]
  by_cases hc : y = x + 1
  · have h1 : ¬ (1 < y - x) := by omega
    have hF : MatedCRTHarmonic.MatedCRT.IsEdge ε ω (x, y, false) :=
      ⟨hxy, Or.inl ⟨hc, rfl⟩⟩
    have hT : ¬ MatedCRTHarmonic.MatedCRT.IsEdge ε ω (x, y, true) := by
      rintro ⟨-, ⟨-, h⟩ | ⟨h, -⟩⟩
      · exact Bool.noConfusion h
      · exact h hc
    have hL : bmAdjacent ε (fun t => (ω t).1) x y := by
      rw [hc]
      exact bmAdjacent_succ hε (continuous_fst.comp ω.continuous) x
    simp only [bmEdgeCount, hne, hmin, hmax, h1, hL, hF, hT, false_and, true_or,
      ↓reduceIte]
  · have hxy' : x + 1 < y := by omega
    have h1 : 1 < y - x := by omega
    have hT := isEdge_iff_bmAdjacent ε ω hxy' true
    have hF := isEdge_iff_bmAdjacent ε ω hxy' false
    simp only [Bool.false_eq_true, ↓reduceIte] at hT hF
    simp only [bmEdgeCount, hne, hmin, hmax, h1, true_and, ↓reduceIte]
    by_cases hL : bmAdjacent ε (fun t => (ω t).1) x y <;>
    by_cases hR : bmAdjacent ε (fun t => (ω t).2) x y <;>
    simp [hL, hR, hT, hF]

open Classical in
/-- The number of sides of the labelled edges joining `x` and `y`, as `Nat.card`, is the
cardinality of the corresponding finite set of sides. -/
theorem nat_card_isEdge_eq_card_filter (ε : ℝ) (ω : MatedCRTHarmonic.MatedCRT.Path2) (x y : ℤ) :
    Nat.card {s : Bool // MatedCRTHarmonic.MatedCRT.IsEdge ε ω (x, y, s)} =
      (Finset.univ.filter fun s : Bool => MatedCRTHarmonic.MatedCRT.IsEdge ε ω (x, y, s)).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- For `ε ≥ 0` and vertices `x < y`, the edge multiplicity `S.mult ε ω x y` of the mated-CRT map
of an environment (Definition 1.1) is the number of labelled edges `(x, y, side)` of
Gwynne–Miller–Sheffield (2019), (1.1), for the boundary-length pair `S.bm ω`. -/
theorem MatedCRTEnv.mult_eq_nat_card_isEdge {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ε : ℝ} (hε : 0 ≤ ε) (ω : Ω) {x y : ℤ} (hxy : x < y) :
    S.mult ε ω x y =
      Nat.card {s : Bool // MatedCRTHarmonic.MatedCRT.IsEdge ε (S.bm ω) (x, y, s)} := by
  classical
  rw [nat_card_isEdge_eq_card_filter]
  exact bmEdgeCount_eq_card_isEdge hε (S.bm ω) hxy

end MatedCRT
