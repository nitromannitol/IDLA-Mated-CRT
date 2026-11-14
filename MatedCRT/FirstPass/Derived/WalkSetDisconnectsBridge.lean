import MatedCRT.FirstPass.Derived.SrwHitLawSetSeparation
import MatedCRT.FirstPass.Derived.SrwGraphAdjBridge
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VerticesMeeting

/-!
# Separation by the trace of a walk: Bonanno's language and the set disconnection of this repository

The separation statements of Bonanno's mated-CRT layer are phrased with `GraphSeparates Γ U A B` (every
`Γ`-walk from `A` to `B` visits `U`), the trace `traceBefore id I x` before the first visit to `I`, the
simple graph `(MatedCRT.graph ε w h).adj` of the mated-CRT multigraph, and `verticesMeeting J D`. The
disconnection estimates of this repository (the set form of [GMS21, Lemma 3.12],
`SrwHitLawSetSeparation`) use `walkSetDisconnectsBeforeHit m Y I x`, i.e. `graphSetDisconnects` of
`walkTraceBefore x (vHitTime I x)` in `adjGraph m`, and `cellVertices ε η D`. This file identifies the two.

## Main results

* `graphSeparates_iff_graphSetDisconnects`: `GraphSeparates G K Y A ↔ graphSetDisconnects G K Y A`;
* `graphSeparates_traceBefore_iff_walkSetDisconnectsBeforeHit`: the trace form, for `srwGraph m`;
* `graphSeparates_graph_adj_iff_walkSetDisconnectsBeforeHit`: the same for the mated-CRT multigraph of a
  path with cell size `ε ≥ 0` and its edge count `bmEdgeCount`;
* `MatedCRTEnv.walkSetDisconnectsBeforeHit_mult_iff`: the same for the edge count `S.mult ε ω` of an
  environment;
* `verticesMeeting_cell_eq_cellVertices`, `setOf_exists_mem_cell_dist_le_eq_cellVertices`: the vertex
  sets of Bonanno's statements as `cellVertices`.
-/

set_option autoImplicit false

namespace MatedCRT

open Set Metric
open MatedCRTHarmonic MatedCRTHarmonic.HarmonicInfinity

/-- `K` meets every `G`-walk from `Y` to `A` iff `K` disconnects `Y` from `A` (no path in the graph induced on
`Kᶜ`): the set version of `graphSeparates_singleton_iff`. -/
theorem graphSeparates_iff_graphSetDisconnects {V : Type*} (G : SimpleGraph V) (K Y A : Set V) :
    GraphSeparates G K Y A ↔ graphSetDisconnects G K Y A := by
  constructor
  · intro h y hy hyK a ha hak
    refine (graphSeparates_singleton_iff G K A y).1 (fun y' hy' b hb w => h y' ?_ b hb w) hyK a ha hak
    rw [mem_singleton_iff.1 hy']
    exact hy
  · intro h y hy b hb w
    exact (graphSeparates_singleton_iff G K A y).2 (fun hyK a ha hak => h y hy hyK a ha hak) y rfl b hb w

/-- For simple random walk on a multigraph `m`, separation by the trace before the first visit to `I` in
Bonanno's language is `walkSetDisconnectsBeforeHit`. -/
theorem graphSeparates_traceBefore_iff_walkSetDisconnectsBeforeHit (m : ℤ → ℤ → ℕ) (Y I : Set ℤ)
    (x : ℕ → ℤ) :
    GraphSeparates (srwGraph m) (traceBefore id I x) Y I ↔ walkSetDisconnectsBeforeHit m Y I x := by
  rw [walkSetDisconnectsBeforeHit, ← graphSeparates_iff_graphSetDisconnects, traceBefore_id_eq,
    adjGraph_eq_srwGraph]

/-- For the mated-CRT multigraph of a path `w` with cell size `ε ≥ 0`, separation by the trace before the first
visit to `I` in its simple graph is `walkSetDisconnectsBeforeHit` for the edge count `bmEdgeCount`. -/
theorem graphSeparates_graph_adj_iff_walkSetDisconnectsBeforeHit {ε : ℝ}
    {w : MatedCRTHarmonic.MatedCRT.Path2} (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε w)
    (hε : 0 ≤ ε) (Y I : Set ℤ) (x : ℕ → ℤ) :
    GraphSeparates (MatedCRTHarmonic.MatedCRT.graph ε w hlf).adj (traceBefore id I x) Y I ↔
      walkSetDisconnectsBeforeHit (bmEdgeCount ε (fun t => (w t).1) (fun t => (w t).2)) Y I x := by
  rw [graph_adj_eq_srwGraph hlf hε]
  exact graphSeparates_traceBefore_iff_walkSetDisconnectsBeforeHit _ Y I x

/-- For an environment `S`, a cell size `ε ≥ 0` and a sample `ω`, `walkSetDisconnectsBeforeHit` for the edge
count `S.mult ε ω` is separation by the trace before the first visit to `I` in the mated-CRT multigraph of the
boundary-length pair `S.bm ω`. -/
theorem MatedCRTEnv.walkSetDisconnectsBeforeHit_mult_iff {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) {ε : ℝ} (hε : 0 ≤ ε) (ω : Ω)
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω)) (Y I : Set ℤ) (x : ℕ → ℤ) :
    walkSetDisconnectsBeforeHit (S.mult ε ω) Y I x ↔
      GraphSeparates (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf).adj (traceBefore id I x) Y I :=
  (graphSeparates_graph_adj_iff_walkSetDisconnectsBeforeHit hlf hε Y I x).symm

/-- The vertices whose cell `H^ε_{εk}` meets `D`, in Bonanno's notation, are `cellVertices ε η D`. -/
theorem verticesMeeting_cell_eq_cellVertices (ε : ℝ) (η : ℝ → ℂ) (D : Set ℂ) :
    verticesMeeting (cell ε η) D = cellVertices ε η D :=
  rfl

/-- The vertices with a cell point at distance at most `δ` from `z` are `cellVertices ε η (closedBall z δ)`. -/
theorem setOf_exists_mem_cell_dist_le_eq_cellVertices (ε : ℝ) (η : ℝ → ℂ) (z : ℂ) (δ : ℝ) :
    {y : ℤ | ∃ q ∈ cell ε η y, dist q z ≤ δ} = cellVertices ε η (closedBall z δ) :=
  Set.ext fun _ => Iff.rfl

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.graphSeparates_iff_graphSetDisconnects
#print axioms MatedCRT.graphSeparates_traceBefore_iff_walkSetDisconnectsBeforeHit
#print axioms MatedCRT.graphSeparates_graph_adj_iff_walkSetDisconnectsBeforeHit
#print axioms MatedCRT.MatedCRTEnv.walkSetDisconnectsBeforeHit_mult_iff
#print axioms MatedCRT.verticesMeeting_cell_eq_cellVertices
#print axioms MatedCRT.setOf_exists_mem_cell_dist_le_eq_cellVertices
