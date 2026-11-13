import MatedCRT.FirstPass.Derived.HarnackPairEvents
import MatedCRT.FirstPass.Derived.SrwWalkLawBridge
import MatedCRT.FirstPass.Derived.SrwGraphAdjBridge
import MatedCRT.FirstPass.Derived.SrwRingPieces
import MatedCRT.FirstPass.Derived.SrwReversibleSteps

/-!
# The pair events of the Harnack inequality depend on the path only through the edge count

Berestycki–Gwynne (2020), Lemmas 3.9–3.11.  For `ε ≥ 0` the itinerary event `PairItinGood` and the disconnection
event `PairL311Good` of the mesh-`ε` mated-CRT map of a path `ω` and a curve `η` depend on `ω` only through the edge
count `m = bmEdgeCount ε ω.1 ω.2` of Definition 1.1:

* `isLocallyFinite_of_isLocallyFiniteMult`: `ω` is locally finite iff `m` is (the edge count is `0`, `1` or `2`);
* `polarTemplateItinerary_congr`, `lemma311Event_congr`: the walk events of Bonanno's multigraph depend on the graph
  only through its adjacency relation;
* `measurableSet_polarTemplateItinerary_paths`: the itinerary event is a measurable set of vertex paths, so that its
  probability under the edge-end walk is the probability under `srwLaw m`;
* `pairItinGood_iff_of_multEq`, `pairL311Good_iff_of_multEq`: two paths with the same edge count have the same pair
  events.
-/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Metric
open MatedCRTHarmonic MatedCRTHarmonic.HarmonicInfinity MatedCRTHarmonic.Markov MatedCRTHarmonic.CellFamily
open MatedCRTHarmonic.GMSMain.T15A

/-! ## Local finiteness of the edge count -/

/-- The edge count of a continuous path vanishes on no edge of Bonanno's edge type. -/
theorem bmEdgeCount_ne_zero_of_isEdge {ε : ℝ} (hε : 0 ≤ ε) {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (e : MatedCRTHarmonic.MatedCRT.Edge ε ω) :
    bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) e.1.1 e.1.2.1 ≠ 0 := by
  obtain ⟨⟨a, c, b⟩, hlt, hcases⟩ := e
  simp only at hlt hcases ⊢
  have hca : a ≠ c := hlt.ne
  have hadj : bmAdjacent ε (fun t => (ω t).1) a c ∨ bmAdjacent ε (fun t => (ω t).2) a c := by
    rcases hcases with ⟨hc, _⟩ | ⟨_, hSC⟩
    · subst hc
      exact Or.inl (bmAdjacent_succ hε (continuous_fst.comp ω.continuous) a)
    · cases b
      · exact Or.inl ((sideCond_iff_bmAdjacent ε _ a c).1 (by simpa using hSC))
      · exact Or.inr ((sideCond_iff_bmAdjacent ε _ a c).1 (by simpa using hSC))
  unfold bmEdgeCount
  simp only [hca, ite_false, min_eq_left hlt.le, max_eq_right hlt.le, hadj, ite_true]
  split_ifs <;> norm_num

/-- **Local finiteness of the mated-CRT map from the edge count.** For `ε ≥ 0`, a path whose edge count has finitely
many neighbours at every vertex has finitely many edges at every vertex (every pair of vertices carries at most
two edges). -/
theorem isLocallyFinite_of_isLocallyFiniteMult {ε : ℝ} (hε : 0 ≤ ε) {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : IsLocallyFiniteMult (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2))) :
    MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω := by
  intro x
  have hne := bmEdgeCount_ne_zero_of_isEdge (ε := ε) hε (ω := ω)
  refine Set.Finite.of_injOn
    (f := fun e : MatedCRTHarmonic.MatedCRT.Edge ε ω => ((if e.1.1 = x then e.1.2.1 else e.1.1), e.1.2.2))
    (t := {k | bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) x k ≠ 0} ×ˢ (Set.univ : Set Bool))
    ?_ ?_ ((hlf x).prod Set.finite_univ)
  · intro e he
    refine ⟨?_, mem_univ _⟩
    have hlt : e.1.1 < e.1.2.1 := e.2.1
    have he' : e.1.1 = x ∨ e.1.2.1 = x := he
    change bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) x (if e.1.1 = x then e.1.2.1 else e.1.1) ≠ 0
    rcases he' with he' | he'
    · have hif : (if e.1.1 = x then e.1.2.1 else e.1.1) = e.1.2.1 := by simp [he']
      rw [hif, ← he']
      exact hne e
    · have h1 : e.1.1 ≠ x := by omega
      have hif : (if e.1.1 = x then e.1.2.1 else e.1.1) = e.1.1 := by simp [h1]
      rw [hif, bmEdgeCount_symm, ← he']
      exact hne e
  · rintro ⟨⟨a, c, b⟩, hlt, _⟩ ha ⟨⟨a', c', b'⟩, hlt', _⟩ ha' hf
    have ha1 : a = x ∨ c = x := ha
    have ha2 : a' = x ∨ c' = x := ha'
    simp only [Prod.mk.injEq] at hf
    obtain ⟨hk, hb⟩ := hf
    have hlt1 : a < c := hlt
    have hlt2 : a' < c' := hlt'
    have hfin : a = a' ∧ c = c' := by
      split_ifs at hk <;> constructor <;> omega
    obtain ⟨rfl, rfl⟩ := hfin
    have hbb : b = b' := hb
    subst hbb
    rfl

/-! ## The walk events depend on the graph only through its adjacency -/

/-- The polar template itinerary of a path in a cellular embedding depends on the graph only through its adjacency
and on the embedding only through its cells. -/
theorem polarTemplateItinerary_congr {E E' : Type*} {G : LFMultigraph ℤ E} {G' : LFMultigraph ℤ E'} {o : ℤ}
    (H : CellularEmbedding G o) (H' : CellularEmbedding G' o) (hc : H.cell = H'.cell) (ha : G.adj = G'.adj)
    (z : ℂ) (r : ℝ) (X : ℕ → ℤ) :
    PolarTemplateItinerary H z r X ↔ PolarTemplateItinerary H' z r X := by
  have key : ∀ (ϑ : ℝ) (n : ℕ) (α β : ℕ → ℝ), RouteM.IsTemplateWalk H z r ϑ n X α β ↔
      RouteM.IsTemplateWalk H' z r ϑ n X α β := by
    intro ϑ n α β
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
      refine ⟨fun j hj => ?_, h2, h3, h4, h5, h6, h7, fun j hj s hs w hw => ?_⟩
      · rw [← ha]
        exact h1 j hj
      · rw [← hc] at hw
        exact h8 j hj s hs w hw
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
      refine ⟨fun j hj => ?_, h2, h3, h4, h5, h6, h7, fun j hj s hs w hw => ?_⟩
      · rw [ha]
        exact h1 j hj
      · rw [hc] at hw
        exact h8 j hj s hs w hw
  unfold PolarTemplateItinerary
  simp only [key, hc, ha]

/-- The walk event (3.35) depends on the graph only through its adjacency. -/
theorem lemma311Event_congr {E E' : Type*} {G : LFMultigraph ℤ E} {G' : LFMultigraph ℤ E'}
    (ha : G.adj = G'.adj) (J : ℤ → Set ℂ) (z : ℂ) (r : ℝ) (X : ℕ → ℤ) :
    Lemma311Event G J z r X ↔ Lemma311Event G' J z r X := by
  unfold Lemma311Event DisconnectsBeforeHit LFMultigraph.Disconnects
  rw [ha]

/-- **Measurability of the itinerary event on vertex paths.** -/
theorem measurableSet_polarTemplateItinerary_paths {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ}
    (H : CellularEmbedding G o) (z : ℂ) (r : ℝ) :
    MeasurableSet {X : ℕ → ℤ | PolarTemplateItinerary H z r X} := by
  have hset : {X : ℕ → ℤ | PolarTemplateItinerary H z r X} =
      (⋃ n : ℕ, {X : ℕ → ℤ | ∃ ϑ : ℝ, ∃ α β : ℕ → ℝ, RouteM.IsTemplateWalk H z r ϑ n X α β ∧
        ∀ j ≤ n, H.cell (X j) ⊆ annulus z (4 * r / 5) (6 * r / 5)}) ∩
      ⋂ j : ℕ, {X : ℕ → ℤ | G.adj.Adj (X j) (X (j + 1))} := by
    ext X
    simp only [PolarTemplateItinerary, mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_iInter]
    constructor
    · rintro ⟨n, ϑ, α, β, h1, h2, h3⟩
      exact ⟨⟨n, ϑ, α, β, h1, h2⟩, h3⟩
    · rintro ⟨⟨n, ϑ, α, β, h1, h2⟩, h3⟩
      exact ⟨n, ϑ, α, β, h1, h2, h3⟩
  rw [hset]
  refine (MeasurableSet.iUnion fun n => ?_).inter (MeasurableSet.iInter fun j => ?_)
  · refine GoodScales.measurableSet_of_forall_eq_le n ?_
    rintro X X' hagree ⟨ϑ, α, β, hW, hcell⟩
    refine ⟨ϑ, α, β, ⟨fun j hj => ?_, hW.α_zero, hW.β_last, hW.monotone_α, hW.monotone_β, hW.overlap, hW.bounds,
      fun j hj s hs w hw => ?_⟩, fun j hj => ?_⟩
    · rw [← hagree j hj.le, ← hagree (j + 1) hj]
      exact hW.adj j hj
    · rw [← hagree j hj] at hw
      exact hW.near j hj s hs w hw
    · rw [← hagree j hj]
      exact hcell j hj
  · refine GoodScales.measurableSet_of_forall_eq_le (j + 1) ?_
    intro X X' hagree hx
    change G.adj.Adj (X j) (X (j + 1)) at hx
    change G.adj.Adj (X' j) (X' (j + 1))
    rw [← hagree j (by omega), ← hagree (j + 1) le_rfl]
    exact hx

/-! ## The pair events depend on the path only through the edge count -/

/-- A cellular embedding of a graph is a cellular embedding of every graph with the same adjacency. -/
def cellularEmbeddingOfAdjEq {E E' : Type*} {G : LFMultigraph ℤ E} {G' : LFMultigraph ℤ E'} {o : ℤ}
    (H : CellularEmbedding G o) (ha : G.adj = G'.adj) : CellularEmbedding G' o where
  cell := H.cell
  isCompact_cell := H.isCompact_cell
  isConnected_cell := H.isConnected_cell
  interior_cell_nonempty := H.interior_cell_nonempty
  locallyFinite_cell := H.locallyFinite_cell
  iUnion_cell := H.iUnion_cell
  volume_inter_cell := H.volume_inter_cell
  inter_of_adj := fun x y hxy => H.inter_of_adj x y (by rw [ha]; exact hxy)
  zero_mem_root := H.zero_mem_root

theorem cellularEmbeddingOfAdjEq_cell {E E' : Type*} {G : LFMultigraph ℤ E} {G' : LFMultigraph ℤ E'} {o : ℤ}
    (H : CellularEmbedding G o) (ha : G.adj = G'.adj) : (cellularEmbeddingOfAdjEq H ha).cell = H.cell := rfl

/-- **Lower bounds for the edge-end walk transfer between paths with the same edge count**, for every measurable set
of vertex paths. -/
theorem walkLaw_vertexPath_preimage_ge_of_multEq {ε : ℝ} (hε : 0 ≤ ε) {ω ω' : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω) (hlf' : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω')
    (hm : bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) =
      bmEdgeCount ε (fun t => (ω' t).1) (fun t => (ω' t).2))
    (y : ℤ) {A : Set (ℕ → ℤ)} (hA : MeasurableSet A) {q : ENNReal}
    (h : q ≤ (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).walkLaw y
      ((MatedCRTHarmonic.MatedCRT.graph ε ω hlf).vertexPath ⁻¹' A)) :
    q ≤ (MatedCRTHarmonic.MatedCRT.graph ε ω' hlf').walkLaw y
      ((MatedCRTHarmonic.MatedCRT.graph ε ω' hlf').vertexPath ⁻¹' A) := by
  have h1 := h.trans (walkLaw_vertexPath_preimage_le_srwLaw hlf hε y A)
  rw [hm] at h1
  rwa [← srwLaw_bmEdgeCount_apply_eq_walkLaw hlf' hε y hA]

/-- The itinerary event of the mesh-`ε` map of `ω` holds for every path `ω'` with the same edge count. -/
theorem pairItinGood_of_multEq {ε : ℝ} (hε : 0 ≤ ε) {ω ω' : MatedCRTHarmonic.MatedCRT.Path2}
    (hm : bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) =
      bmEdgeCount ε (fun t => (ω' t).1) (fun t => (ω' t).2))
    {η : ℝ → ℂ} {p : ℝ} {z : ℂ} {r : ℝ} (h : PairItinGood ε ω η p z r) : PairItinGood ε ω' η p z r := by
  obtain ⟨hlf, H, hHc, hgood⟩ := h
  have hlf' : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω' := by
    refine isLocallyFinite_of_isLocallyFiniteMult hε ?_
    rw [← hm]
    exact FirstPass.Derived.isLocallyFiniteMult_bmEdgeCount hlf hε
  have hadj : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj =
      (MatedCRTHarmonic.MatedCRT.graph ε ω' hlf').adj := by
    rw [graph_adj_eq_srwGraph hlf hε, graph_adj_eq_srwGraph hlf' hε, hm]
  refine ⟨hlf', cellularEmbeddingOfAdjEq H hadj, hHc, fun y hy => ?_⟩
  have hA := measurableSet_polarTemplateItinerary_paths (cellularEmbeddingOfAdjEq H hadj) z r
  have hEq : {X : ℕ → ℤ | PolarTemplateItinerary H z r X} =
      {X | PolarTemplateItinerary (cellularEmbeddingOfAdjEq H hadj) z r X} := by
    ext X
    exact polarTemplateItinerary_congr H (cellularEmbeddingOfAdjEq H hadj) rfl hadj z r X
  rw [← hEq] at hA
  have key := walkLaw_vertexPath_preimage_ge_of_multEq hε hlf hlf' hm y hA (hgood y hy)
  rw [hEq] at key
  exact key

/-- **The itinerary event depends on the path only through its edge count.** -/
theorem pairItinGood_iff_of_multEq {ε : ℝ} (hε : 0 ≤ ε) {ω ω' : MatedCRTHarmonic.MatedCRT.Path2}
    (hm : bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) =
      bmEdgeCount ε (fun t => (ω' t).1) (fun t => (ω' t).2))
    (η : ℝ → ℂ) (p : ℝ) (z : ℂ) (r : ℝ) : PairItinGood ε ω η p z r ↔ PairItinGood ε ω' η p z r :=
  ⟨pairItinGood_of_multEq hε hm, pairItinGood_of_multEq hε hm.symm⟩

/-- The disconnection event of Lemma 3.11 of the mesh-`ε` map of `ω` holds for every path `ω'` with the same edge
count. -/
theorem pairL311Good_of_multEq {ε : ℝ} (hε : 0 ≤ ε) {ω ω' : MatedCRTHarmonic.MatedCRT.Path2}
    (hm : bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) =
      bmEdgeCount ε (fun t => (ω' t).1) (fun t => (ω' t).2))
    {η : ℝ → ℂ} {ρ'' f p : ℝ} (h : PairL311Good ε ω η ρ'' f p) : PairL311Good ε ω' η ρ'' f p := by
  obtain ⟨hlf, H, hHc, hgood⟩ := h
  have hlf' : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω' := by
    refine isLocallyFinite_of_isLocallyFiniteMult hε ?_
    rw [← hm]
    exact FirstPass.Derived.isLocallyFiniteMult_bmEdgeCount hlf hε
  have hadj : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj =
      (MatedCRTHarmonic.MatedCRT.graph ε ω' hlf').adj := by
    rw [graph_adj_eq_srwGraph hlf hε, graph_adj_eq_srwGraph hlf' hε, hm]
  refine ⟨hlf', cellularEmbeddingOfAdjEq H hadj, hHc, fun w r hfr hrρ hball y hy => ?_⟩
  have hA := measurableSet_lemma311Event_paths (MatedCRTHarmonic.MatedCRT.graph ε ω' hlf')
    (cellularEmbeddingOfAdjEq H hadj).cell w r
  have hEq : {X : ℕ → ℤ | Lemma311Event (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) H.cell w r X} =
      {X | Lemma311Event (MatedCRTHarmonic.MatedCRT.graph ε ω' hlf') (cellularEmbeddingOfAdjEq H hadj).cell w r X} := by
    ext X
    exact lemma311Event_congr hadj H.cell w r X
  rw [← hEq] at hA
  have key := walkLaw_vertexPath_preimage_ge_of_multEq hε hlf hlf' hm y hA (hgood w r hfr hrρ hball y hy)
  rw [hEq] at key
  exact key

/-- **The disconnection event of Lemma 3.11 depends on the path only through its edge count.** -/
theorem pairL311Good_iff_of_multEq {ε : ℝ} (hε : 0 ≤ ε) {ω ω' : MatedCRTHarmonic.MatedCRT.Path2}
    (hm : bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) =
      bmEdgeCount ε (fun t => (ω' t).1) (fun t => (ω' t).2))
    (η : ℝ → ℂ) (ρ'' f p : ℝ) : PairL311Good ε ω η ρ'' f p ↔ PairL311Good ε ω' η ρ'' f p :=
  ⟨pairL311Good_of_multEq hε hm, pairL311Good_of_multEq hε hm.symm⟩

end MatedCRT

/-! ## Audit -/
#print axioms MatedCRT.isLocallyFinite_of_isLocallyFiniteMult
#print axioms MatedCRT.measurableSet_polarTemplateItinerary_paths
#print axioms MatedCRT.pairItinGood_iff_of_multEq
#print axioms MatedCRT.pairL311Good_iff_of_multEq
