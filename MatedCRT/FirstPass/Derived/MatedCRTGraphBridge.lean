import MatedCRT.Defs.Setting
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTGraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VerticesMeeting
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Energy

/-!
# The mated-CRT map as Bonanno's locally finite multigraph

The `ε`-mated-CRT map of Definition 1.1 appears in two forms: in the statements of this
formalization through its edge multiplicity `bmEdgeCount ε L R` (`MatedCRTEnv.mult`), and in
Leonardo Bonanno's development (adapted in Lattice-Probability) as the locally finite multigraph
`MatedCRTHarmonic.MatedCRT.graph ε ω h` with an explicit edge type. This file identifies them:

* `card_filter_outDarts_graph`: the number of darts of the multigraph from `x` to `y` is
  `bmEdgeCount ε L R x y`, for the boundary-length pair `(L, R)` of `ω` and `ε ≥ 0`;
* `deg_graph_eq`, `lap_graph_eq`: the degree is `mdeg`, and the unnormalized graph Laplacian is
  `∑_y m(x, y) (f(x) - f(y))`;
* `lap_graph_eq_zero_iff`: discrete harmonicity in Bonanno's sense (`GMS3.lap = 0`) is
  harmonicity for the degree normalized Laplacian `matedLaplacian`;
* `verticesMeeting_cell`: Bonanno's `verticesMeeting` of the cells is `cellVertices`.

The only analytic input is that consecutive vertices are always adjacent for continuous paths
(`bmAdjacent_succ`), which is how Bonanno's edge type hard-wires the edge `(x, x + 1)`.
-/

open Set Function

namespace MatedCRT

/-- Bonanno's side condition is the adjacency condition (eq:edge-map). -/
theorem sideCond_iff_bmAdjacent (ε : ℝ) (X : ℝ → ℝ) (j k : ℤ) :
    MatedCRTHarmonic.MatedCRT.SideCond ε X j k ↔ bmAdjacent ε X j k := by
  simp only [MatedCRTHarmonic.MatedCRT.SideCond, MatedCRTHarmonic.MatedCRT.intervalInf,
    bmAdjacent, mul_sub, mul_one]

/-- For a continuous path and `ε ≥ 0`, consecutive vertices satisfy the adjacency condition. -/
theorem bmAdjacent_succ {ε : ℝ} (hε : 0 ≤ ε) {X : ℝ → ℝ} (hX : Continuous X) (j : ℤ) :
    bmAdjacent ε X j (j + 1) := by
  have hj : ε * ((j + 1 : ℤ) : ℝ) - ε = ε * j := by push_cast; ring
  have hb : ∀ a b : ℝ, BddBelow (X '' Icc a b) := fun a b => (isCompact_Icc.image hX).bddBelow
  unfold bmAdjacent
  rw [hj, Icc_self, image_singleton, csInf_singleton]
  refine max_le (csInf_le (hb _ _) ⟨ε * j, ⟨by linarith, le_rfl⟩, rfl⟩)
    (csInf_le (hb _ _) ⟨ε * j, ⟨le_rfl, ?_⟩, rfl⟩)
  push_cast
  rw [mul_add, mul_one]
  linarith

section Graph

variable {ε : ℝ} {ω : MatedCRTHarmonic.MatedCRT.Path2}
  (h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)

theorem graph_dsrc (e : MatedCRTHarmonic.MatedCRT.Edge ε ω) (b : Bool) :
    (MatedCRTHarmonic.MatedCRT.graph ε ω h).dsrc (e, b) = if b then e.1.2.1 else e.1.1 := by
  cases b <;> rfl

theorem graph_dtgt (e : MatedCRTHarmonic.MatedCRT.Edge ε ω) (b : Bool) :
    (MatedCRTHarmonic.MatedCRT.graph ε ω h).dtgt (e, b) = if b then e.1.1 else e.1.2.1 := by
  cases b <;> rfl

/-- **Edge multiplicity of Bonanno's mated-CRT multigraph.** For `ε ≥ 0`, the number of darts
from `x` to `y` is the edge count `bmEdgeCount ε L R x y` of Definition 1.1. -/
theorem card_filter_outDarts_graph (hε : 0 ≤ ε) (x y : ℤ) :
    (((MatedCRTHarmonic.MatedCRT.graph ε ω h).outDarts x).filter
        (fun d => (MatedCRTHarmonic.MatedCRT.graph ε ω h).dtgt d = y)).card =
      bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) x y := by
  classical
  set G := MatedCRTHarmonic.MatedCRT.graph ε ω h with hG
  have hmemF : ∀ d : G.Dart, d ∈ (G.outDarts x).filter (fun d => G.dtgt d = y) ↔
      G.dsrc d = x ∧ G.dtgt d = y := fun d => by
    rw [Finset.mem_filter, MatedCRTHarmonic.Harmonic.mem_outDarts]
  have hinj : Set.InjOn (fun d : G.Dart => d.1.1.2.2)
      ((G.outDarts x).filter (fun d => G.dtgt d = y) : Set G.Dart) := by
    rintro ⟨⟨⟨a, c, t⟩, he⟩, b⟩ hd ⟨⟨⟨a', c', t'⟩, he'⟩, b'⟩ hd' hs
    rw [Finset.mem_coe, hmemF, graph_dsrc, graph_dtgt] at hd hd'
    simp only at hs
    subst hs
    have hlt : a < c := he.1
    have hlt' : a' < c' := he'.1
    cases b <;> cases b' <;> simp only [Bool.false_eq_true, ↓reduceIte] at hd hd'
    · obtain ⟨rfl, rfl⟩ := hd; obtain ⟨rfl, rfl⟩ := hd'; rfl
    · omega
    · omega
    · obtain ⟨rfl, rfl⟩ := hd; obtain ⟨rfl, rfl⟩ := hd'; rfl
  have himage : ((G.outDarts x).filter (fun d => G.dtgt d = y)).image
      (fun d : G.Dart => d.1.1.2.2) = Finset.univ.filter
        (fun t => x ≠ y ∧ MatedCRTHarmonic.MatedCRT.IsEdge ε ω (min x y, max x y, t)) := by
    ext t
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨⟨⟨a, c, t'⟩, he⟩, b⟩, hd, rfl⟩
      rw [MatedCRTHarmonic.Harmonic.mem_outDarts, graph_dsrc, graph_dtgt] at hd
      have hlt : a < c := he.1
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hd <;> obtain ⟨rfl, rfl⟩ := hd
      · exact ⟨hlt.ne, by rw [min_eq_left hlt.le, max_eq_right hlt.le]; exact he⟩
      · exact ⟨hlt.ne', by rw [min_eq_right hlt.le, max_eq_left hlt.le]; exact he⟩
    · rintro ⟨hxy, he⟩
      rcases lt_or_gt_of_ne hxy with hlt | hlt
      · rw [min_eq_left hlt.le, max_eq_right hlt.le] at he
        refine ⟨(⟨(x, y, t), he⟩, false), ?_, rfl⟩
        rw [MatedCRTHarmonic.Harmonic.mem_outDarts, graph_dsrc, graph_dtgt]
        simp
      · rw [min_eq_right hlt.le, max_eq_left hlt.le] at he
        refine ⟨(⟨(y, x, t), he⟩, true), ?_, rfl⟩
        rw [MatedCRTHarmonic.Harmonic.mem_outDarts, graph_dsrc, graph_dtgt]
        simp
  rw [← Finset.card_image_of_injOn hinj, himage, Finset.card_filter, Fintype.sum_bool]
  have hLc : Continuous fun t => (ω t).1 := continuous_fst.comp ω.continuous
  unfold bmEdgeCount
  by_cases hxy : x = y
  · simp [hxy]
  · have hlt : min x y < max x y := min_lt_max.2 hxy
    simp only [hxy, ne_eq, not_false_eq_true, true_and,
      MatedCRTHarmonic.MatedCRT.IsEdge, hlt, Bool.false_eq_true, ↓reduceIte, and_true,
      and_false, Bool.true_eq_false, false_or, sideCond_iff_bmAdjacent]
    by_cases hsucc : max x y = min x y + 1
    · simp [hsucc, bmAdjacent_succ hε hLc (min x y)]
    · have h1 : 1 < max x y - min x y := by omega
      by_cases hL : bmAdjacent ε (fun t => (ω t).1) (min x y) (max x y) <;>
        by_cases hR : bmAdjacent ε (fun t => (ω t).2) (min x y) (max x y) <;>
        simp [hsucc, hL, hR, h1]

/-- The darts out of `x` end in the support of the edge count. -/
theorem bmEdgeCount_ne_zero_mem_image (hε : 0 ≤ ε) {x y : ℤ}
    (hy : bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) x y ≠ 0) :
    y ∈ ((MatedCRTHarmonic.MatedCRT.graph ε ω h).outDarts x).image
      (MatedCRTHarmonic.MatedCRT.graph ε ω h).dtgt := by
  rw [← card_filter_outDarts_graph h hε, Finset.card_ne_zero] at hy
  obtain ⟨d, hd⟩ := hy
  rw [Finset.mem_filter] at hd
  exact Finset.mem_image.2 ⟨d, hd.1, hd.2⟩

/-- The degree of Bonanno's mated-CRT multigraph is `mdeg` of the edge count. -/
theorem deg_graph_eq (hε : 0 ≤ ε) (x : ℤ) :
    (MatedCRTHarmonic.MatedCRT.graph ε ω h).deg x =
      mdeg (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x := by
  set G := MatedCRTHarmonic.MatedCRT.graph ε ω h with hG
  have hsupp : (support fun y => bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) x y) ⊆
      ↑((G.outDarts x).image G.dtgt) := fun y hy => bmEdgeCount_ne_zero_mem_image h hε hy
  unfold MatedCRTHarmonic.LFMultigraph.deg mdeg
  rw [finsum_eq_sum_of_support_subset _ hsupp,
    Finset.card_eq_sum_card_fiberwise (f := G.dtgt) (t := (G.outDarts x).image G.dtgt)
      (fun d hd => Finset.mem_image_of_mem _ hd)]
  exact Finset.sum_congr rfl fun y _ => card_filter_outDarts_graph h hε x y

/-- Bonanno's unnormalized graph Laplacian of the mated-CRT multigraph is
`∑_y m(x, y) (f(x) - f(y))` for the edge count `m` of Definition 1.1. -/
theorem lap_graph_eq (hε : 0 ≤ ε) (f : ℤ → ℝ) (x : ℤ) :
    MatedCRTHarmonic.GMS3.lap (MatedCRTHarmonic.MatedCRT.graph ε ω h) f x =
      ∑ᶠ y, (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) x y : ℝ) * (f x - f y) := by
  set G := MatedCRTHarmonic.MatedCRT.graph ε ω h with hG
  have hsupp : (support fun y =>
      (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) x y : ℝ) * (f x - f y)) ⊆
      ↑((G.outDarts x).image G.dtgt) := by
    intro y hy
    refine bmEdgeCount_ne_zero_mem_image h hε fun h0 => hy ?_
    simp [h0]
  rw [finsum_eq_sum_of_support_subset _ hsupp, MatedCRTHarmonic.GMS3.lap,
    ← Finset.sum_fiberwise_of_maps_to (g := G.dtgt) (t := (G.outDarts x).image G.dtgt)
      (fun d hd => Finset.mem_image_of_mem _ hd)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← card_filter_outDarts_graph h hε,
    Finset.sum_congr rfl (fun d hd => by rw [(Finset.mem_filter.1 hd).2]),
    Finset.sum_const, nsmul_eq_mul]

/-- **Discrete harmonicity agrees.** For `ε ≥ 0`, `f` is discrete harmonic at `x` for
Bonanno's mated-CRT multigraph (`GMS3.lap = 0`) iff the degree normalized Laplacian
`matedLaplacian` of the edge count vanishes at `x`. -/
theorem lap_graph_eq_zero_iff (hε : 0 ≤ ε) (f : ℤ → ℝ) (x : ℤ) :
    MatedCRTHarmonic.GMS3.lap (MatedCRTHarmonic.MatedCRT.graph ε ω h) f x = 0 ↔
      matedLaplacian (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) f x = 0 := by
  set G := MatedCRTHarmonic.MatedCRT.graph ε ω h with hG
  have hpos : 0 < G.deg x := by
    unfold MatedCRTHarmonic.LFMultigraph.deg
    exact Finset.card_pos.2 ⟨(⟨(x, x + 1, false), lt_add_one x, Or.inl ⟨rfl, rfl⟩⟩, false),
      (MatedCRTHarmonic.Harmonic.mem_outDarts G).2 rfl⟩
  have hdeg : ((mdeg (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x : ℕ) : ℝ) ≠ 0 := by
    rw [← deg_graph_eq h hε]
    exact_mod_cast hpos.ne'
  have hneg : (∑ᶠ y, (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) x y : ℝ) *
      (f y - f x)) = -∑ᶠ y, (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) x y : ℝ) *
      (f x - f y) := by
    rw [← finsum_neg_distrib]
    exact finsum_congr fun y => by ring
  rw [matedLaplacian, mLaplacian, lap_graph_eq h hε, mul_eq_zero, inv_eq_zero, hneg, neg_eq_zero]
  simp [hdeg]

end Graph

/-- For a mated-CRT environment, Bonanno's discrete harmonicity on the multigraph of the
Brownian pair `S.bm ω` is harmonicity for `matedLaplacian (S.mult ε ω)`. -/
theorem MatedCRTEnv.lap_graph_eq_zero_iff {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ε : ℝ} (hε : 0 ≤ ε) {ω : Ω} (h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
    (f : ℤ → ℝ) (x : ℤ) :
    MatedCRTHarmonic.GMS3.lap (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) h) f x = 0 ↔
      matedLaplacian (S.mult ε ω) f x = 0 :=
  MatedCRT.lap_graph_eq_zero_iff h hε f x

/-- For a mated-CRT environment, the degree of Bonanno's multigraph is `matedDeg`. -/
theorem MatedCRTEnv.deg_graph_eq {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ε : ℝ} (hε : 0 ≤ ε) {ω : Ω} (h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
    (x : ℤ) :
    (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) h).deg x = matedDeg (S.mult ε ω) x :=
  MatedCRT.deg_graph_eq h hε x

/-- Bonanno's `verticesMeeting` of the cells is `cellVertices`. -/
theorem verticesMeeting_cell (ε : ℝ) (η : ℝ → ℂ) (D : Set ℂ) :
    MatedCRTHarmonic.verticesMeeting (cell ε η) D = cellVertices ε η D :=
  rfl

end MatedCRT
