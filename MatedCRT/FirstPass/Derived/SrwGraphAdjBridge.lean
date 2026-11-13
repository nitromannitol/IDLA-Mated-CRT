import MatedCRT.FirstPass.Derived.MatedCRTGraphBridge
import MatedCRT.FirstPass.Derived.SrwChainBridge
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Disconnects

/-!
# Adjacency of the mated-CRT multigraph and of the graph of its edge count

For `ε ≥ 0` the simple graph underlying the locally finite mated-CRT multigraph `G^ε` (two vertices adjacent when an
edge joins them, loops ignored) is `srwGraph (bmEdgeCount ε L R)`: the edge count `bmEdgeCount ε L R x y` is the number
of darts from `x` to `y`, so it is nonzero exactly when an edge joins `x` and `y`.  Consequently a vertex set
`U` disconnects `S` from `T` in the multigraph (every graph path from `S` to `T` visits `U`) exactly when it separates
`S` from `T` in `srwGraph (bmEdgeCount ε L R)`.
-/

set_option autoImplicit false

namespace MatedCRT

variable {ε : ℝ} {ω : MatedCRTHarmonic.MatedCRT.Path2} (h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
include h

/-- A nonzero edge count between `x` and `y` means a dart from `x` to `y`, and conversely. -/
theorem bmEdgeCount_ne_zero_iff_exists_dart (hε : 0 ≤ ε) (x y : ℤ) :
    bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) x y ≠ 0 ↔
      ∃ d : (MatedCRTHarmonic.MatedCRT.graph ε ω h).Dart,
        (MatedCRTHarmonic.MatedCRT.graph ε ω h).dsrc d = x ∧
          (MatedCRTHarmonic.MatedCRT.graph ε ω h).dtgt d = y := by
  classical
  rw [← card_filter_outDarts_graph h hε, Finset.card_ne_zero]
  constructor
  · rintro ⟨d, hd⟩
    rw [Finset.mem_filter, MatedCRTHarmonic.Harmonic.mem_outDarts] at hd
    exact ⟨d, hd.1, hd.2⟩
  · rintro ⟨d, hd1, hd2⟩
    refine ⟨d, ?_⟩
    rw [Finset.mem_filter, MatedCRTHarmonic.Harmonic.mem_outDarts]
    exact ⟨hd1, hd2⟩

/-- A dart from `x` to `y` is an edge between them, in either direction. -/
theorem exists_dart_iff_exists_edge (x y : ℤ) :
    (∃ d : (MatedCRTHarmonic.MatedCRT.graph ε ω h).Dart,
        (MatedCRTHarmonic.MatedCRT.graph ε ω h).dsrc d = x ∧
          (MatedCRTHarmonic.MatedCRT.graph ε ω h).dtgt d = y) ↔
      ∃ e, ((MatedCRTHarmonic.MatedCRT.graph ε ω h).src e = x ∧ (MatedCRTHarmonic.MatedCRT.graph ε ω h).tgt e = y) ∨
        ((MatedCRTHarmonic.MatedCRT.graph ε ω h).tgt e = x ∧ (MatedCRTHarmonic.MatedCRT.graph ε ω h).src e = y) := by
  set G := MatedCRTHarmonic.MatedCRT.graph ε ω h with hG
  constructor
  · rintro ⟨⟨e, b⟩, h1, h2⟩
    refine ⟨e, ?_⟩
    cases b
    · left
      simpa [MatedCRTHarmonic.LFMultigraph.dsrc, MatedCRTHarmonic.LFMultigraph.dtgt] using And.intro h1 h2
    · right
      simpa [MatedCRTHarmonic.LFMultigraph.dsrc, MatedCRTHarmonic.LFMultigraph.dtgt] using And.intro h1 h2
  · rintro ⟨e, h1 | h1⟩
    · exact ⟨(e, false), by simpa [MatedCRTHarmonic.LFMultigraph.dsrc] using h1.1,
        by simpa [MatedCRTHarmonic.LFMultigraph.dtgt] using h1.2⟩
    · exact ⟨(e, true), by simpa [MatedCRTHarmonic.LFMultigraph.dsrc] using h1.1,
        by simpa [MatedCRTHarmonic.LFMultigraph.dtgt] using h1.2⟩

/-- **The graph underlying the mated-CRT multigraph is `srwGraph` of the edge count.** -/
theorem graph_adj_eq_srwGraph (hε : 0 ≤ ε) :
    (MatedCRTHarmonic.MatedCRT.graph ε ω h).adj =
      srwGraph (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) := by
  ext x y
  simp only [MatedCRTHarmonic.LFMultigraph.adj, SimpleGraph.fromRel_adj, srwGraph]
  rw [bmEdgeCount_ne_zero_iff_exists_dart h hε, bmEdgeCount_ne_zero_iff_exists_dart h hε,
    exists_dart_iff_exists_edge h, exists_dart_iff_exists_edge h]
  constructor
  · rintro ⟨hne, he | he⟩
    · exact ⟨hne, Or.inl (by obtain ⟨e, he⟩ := he; exact ⟨e, Or.inl he⟩)⟩
    · exact ⟨hne, Or.inl (by obtain ⟨e, he⟩ := he; exact ⟨e, Or.inr ⟨he.2, he.1⟩⟩)⟩
  · rintro ⟨hne, ⟨e, he | he⟩ | ⟨e, he | he⟩⟩
    · exact ⟨hne, Or.inl ⟨e, he⟩⟩
    · exact ⟨hne, Or.inr ⟨e, he.2, he.1⟩⟩
    · exact ⟨hne, Or.inr ⟨e, he⟩⟩
    · exact ⟨hne, Or.inl ⟨e, he.2, he.1⟩⟩

/-- A vertex set disconnects `S` from `T` in the mated-CRT multigraph exactly when it separates them in the simple
graph of the edge count. -/
theorem disconnects_graph_iff_graphSeparates (hε : 0 ≤ ε) (U S T : Set ℤ) :
    (MatedCRTHarmonic.MatedCRT.graph ε ω h).Disconnects U S T ↔
      MatedCRTHarmonic.HarmonicInfinity.GraphSeparates
        (srwGraph (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2))) U S T := by
  unfold MatedCRTHarmonic.LFMultigraph.Disconnects MatedCRTHarmonic.HarmonicInfinity.GraphSeparates
  rw [graph_adj_eq_srwGraph h hε]

end MatedCRT

/-! ## Audit -/
#print axioms MatedCRT.bmEdgeCount_ne_zero_iff_exists_dart
#print axioms MatedCRT.exists_dart_iff_exists_edge
#print axioms MatedCRT.graph_adj_eq_srwGraph
#print axioms MatedCRT.disconnects_graph_iff_graphSeparates
