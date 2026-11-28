import MatedCRT.FirstPass.Derived.ZeroConePolygonalCells

/-!
# The fan triangulation of the Voronoi tiles

Let `V` be a locally finite set of sites dense relative to a scale function `r`
(`IsSiteSystem V r`). The tile `Q_p` is a compact convex polygon with `p` in its interior; its edges
are the facets `facet V p q = Q_p ∩ Q_q` which are not reduced to a point. The fan triangle
`fan V p q` is the convex hull of the site `p` and such a facet (the triangle spanned by `p` and an
edge of its tile). These triangles are the pieces of the piecewise affine homeomorphisms of the
written measurability argument (answer `notes/mq-idla-rig35b-measurable-answer.md`, section 2:
"triangulate the square using the split arrangement edges as constraints").

* `facet V p q`, `IsFanPair V p q`, `fan V p q`, `fanVerts V p q`: the facet, the pairs with a
  nondegenerate facet, the fan triangle and its vertex set `{p} ∪ ext (facet V p q)`.
* `IsSiteSystem.tile_eq_iUnion_fan`: the tile is the union of its fan triangles (star-shapedness
  from `p`; every frontier point lies on a nondegenerate facet).
* `IsSiteSystem.finite_fanPairs_meeting`: only finitely many fan triangles meet a compact set.
* `fan_inter_fan`: two distinct fan triangles meet in the convex hull of their common vertices:
  empty, a common vertex, a common edge (a facet shared by `fan V p q` and `fan V q p`, or a spoke
  `[p, v]` shared by two triangles of the same tile).
* `IsSiteSystem.frontier_tile_eq_iUnion_facet`,
  `IsSiteSystem.tileVertices_subset_extremePoints_facet`, `IsSiteSystem.shared_eq_iUnion_edges`:
  the frontier of a tile and its spokes are unions of triangle edges.
* `PolygonalInput.cell_eq_iUnion`: each polygonal cell is a union of fan triangles (of the tiles it
  owns) and fan triangle edges.
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open ReflectedGMS

variable {V : Set Plane} {r : Plane → ℝ}

/-! ## Facets of the tiles -/

/-- **The facet** `Q_p ∩ Q_q` of two tiles. -/
def facet (V : Set Plane) (p q : Plane) : Set Plane := tile V p ∩ tile V q

theorem facet_comm (V : Set Plane) (p q : Plane) : facet V p q = facet V q p := inter_comm _ _

theorem facet_subset_left (V : Set Plane) (p q : Plane) : facet V p q ⊆ tile V p :=
  inter_subset_left

theorem facet_subset_right (V : Set Plane) (p q : Plane) : facet V p q ⊆ tile V q :=
  inter_subset_right

theorem convex_facet (V : Set Plane) (p q : Plane) : Convex ℝ (facet V p q) :=
  (convex_tile V p).inter (convex_tile V q)

theorem IsSiteSystem.isCompact_facet (hV : IsSiteSystem V r) (p q : Plane) :
    IsCompact (facet V p q) :=
  (hV.isCompact_tile p).inter_right (isClosed_tile V q)

theorem mem_facet_iff {p q y : Plane} (hp : p ∈ V) (hq : q ∈ V) :
    y ∈ facet V p q ↔ y ∈ tile V p ∧ dist y p = dist y q := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, le_antisymm (h1 q hq) (h2 p hp)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun s hs => by rw [← h2]; exact h1 s hs⟩

theorem bisector_swap (p q y : Plane) : bisector q p y = -bisector p q y := by
  unfold bisector
  rw [show p - q = -(q - p) from (neg_sub q p).symm, inner_neg_right]
  ring

theorem bisector_eq_zero_iff {p q y : Plane} : bisector p q y = 0 ↔ dist y p = dist y q := by
  have h1 := dist_le_dist_iff_bisector p q y
  have h2 := dist_le_dist_iff_bisector q p y
  rw [bisector_swap] at h2
  constructor
  · intro h
    exact le_antisymm (h1.2 h.ge) (h2.2 (by rw [h]; simp))
  · intro h
    have a := h1.1 h.le
    have b := h2.1 h.ge
    linarith

theorem mem_facet_iff_bisector {p q y : Plane} (hp : p ∈ V) (hq : q ∈ V) :
    y ∈ facet V p q ↔ y ∈ tile V p ∧ bisector p q y = 0 := by
  rw [mem_facet_iff hp hq, bisector_eq_zero_iff]

theorem facet_subset_frontier {p q : Plane} (hp : p ∈ V) (hq : q ∈ V) (hpq : p ≠ q) :
    facet V p q ⊆ frontier (tile V p) := fun _ hy =>
  mem_frontier_of_mem_tile_inter V hp hq hpq hy.1 hy.2

/-- A tile meeting a facet with a site `q` has `q` among the sites near `p`. -/
theorem IsSiteSystem.mem_nearSites_of_mem_facet (hV : IsSiteSystem V r) {p q y : Plane} (hp : p ∈ V)
    (hq : q ∈ V) (hy : y ∈ facet V p q) : q ∈ nearSites V p (r p / 99 + 1) := by
  refine ⟨hq, mem_closedBall.2 ?_⟩
  have h := hV.dist_le hy.1
  have e := ((mem_facet_iff hp hq).1 hy).2
  have := dist_triangle q y p
  rw [dist_comm q y] at this
  linarith

/-! ## Star-shapedness of a tile -/

theorem IsSiteSystem.self_mem_interior_tile (hV : IsSiteSystem V r) (p : Plane) :
    p ∈ interior (tile V p) := by
  obtain ⟨ε, hε, hball⟩ := hV.exists_ball_subset_tile p
  exact interior_maximal hball isOpen_ball (mem_ball_self hε)

/-- A point of a segment from the site `p` to a point `f` of its tile which lies in the frontier
of the tile is the endpoint `f`. -/
theorem IsSiteSystem.eq_of_mem_segment_of_mem_frontier (hV : IsSiteSystem V r) (p : Plane)
    {f x : Plane} (hf : f ∈ tile V p) (hx : x ∈ segment ℝ p f)
    (hxf : x ∈ frontier (tile V p)) : x = f := by
  by_contra hne
  by_cases hxp : x = p
  · subst hxp
    exact hxf.2 (hV.self_mem_interior_tile x)
  · exact hxf.2 ((convex_tile V p).openSegment_interior_self_subset_interior
      (hV.self_mem_interior_tile p) hf
      (mem_openSegment_of_ne_left_right (Ne.symm hxp) (Ne.symm hne) hx))

/-- Every ray from the site `p` leaves the tile at a frontier point. -/
theorem IsSiteSystem.exists_exit (hV : IsSiteSystem V r) (p : Plane) {u : Plane} (hu : u ≠ 0) :
    ∃ s : ℝ, 0 < s ∧ p + s • u ∈ frontier (tile V p) ∧
      ∀ t : ℝ, 0 ≤ t → p + t • u ∈ tile V p → t ≤ s := by
  have hun : 0 < ‖u‖ := norm_pos_iff.2 hu
  set M : ℝ := r p / (99 * ‖u‖) with hM
  have hbound : ∀ t : ℝ, 0 ≤ t → p + t • u ∈ tile V p → t ≤ M := by
    intro t ht hmem
    have h := hV.dist_le hmem
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht] at h
    rw [hM, le_div_iff₀ (by positivity)]
    linarith
  have hcont : Continuous fun t : ℝ => p + t • u := by fun_prop
  have hcpt : IsCompact {t : ℝ | 0 ≤ t ∧ p + t • u ∈ tile V p} := by
    have : {t : ℝ | 0 ≤ t ∧ p + t • u ∈ tile V p} =
        Icc 0 M ∩ (fun t : ℝ => p + t • u) ⁻¹' tile V p := by
      ext t
      constructor
      · rintro ⟨h0, h1⟩
        exact ⟨⟨h0, hbound t h0 h1⟩, h1⟩
      · rintro ⟨⟨h0, -⟩, h1⟩
        exact ⟨h0, h1⟩
    rw [this]
    exact isCompact_Icc.inter_right ((isClosed_tile V p).preimage hcont)
  obtain ⟨s, hs, hgr⟩ := hcpt.exists_isGreatest ⟨0, le_rfl, by simpa using self_mem_tile V p⟩
  have hspos : 0 < s := by
    obtain ⟨ε, hε, hball⟩ := hV.exists_ball_subset_tile p
    have ht : ε / (2 * ‖u‖) ∈ {t : ℝ | 0 ≤ t ∧ p + t • u ∈ tile V p} := by
      refine ⟨by positivity, hball ?_⟩
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg (by positivity)]
      field_simp
      linarith
    exact lt_of_lt_of_le (by positivity) (hgr ht)
  refine ⟨s, hspos, ⟨subset_closure hs.2, fun hint => ?_⟩, fun t ht1 ht2 => hgr ⟨ht1, ht2⟩⟩
  have hopen : IsOpen ((fun t : ℝ => p + t • u) ⁻¹' interior (tile V p)) :=
    isOpen_interior.preimage hcont
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen s hint
  have hmem : s + ε / 2 ∈ (fun t : ℝ => p + t • u) ⁻¹' interior (tile V p) := hball (by
    rw [mem_ball, Real.dist_eq]
    rw [show s + ε / 2 - s = ε / 2 by ring, abs_of_pos (by positivity)]
    linarith)
  have := hgr ⟨by linarith, interior_subset hmem⟩
  linarith

/-- Every point of the tile other than the site lies on a segment from the site to a frontier
point. -/
theorem IsSiteSystem.exists_frontier_of_mem_tile (hV : IsSiteSystem V r) {p x : Plane}
    (hx : x ∈ tile V p) (hxp : x ≠ p) : ∃ f ∈ frontier (tile V p), x ∈ segment ℝ p f := by
  obtain ⟨s, hs0, hsf, hsmax⟩ := hV.exists_exit p (sub_ne_zero.2 hxp)
  have h1 : 1 ≤ s := hsmax 1 zero_le_one (by simpa using hx)
  refine ⟨_, hsf, 1 - s⁻¹, s⁻¹, sub_nonneg.2 (inv_le_one_of_one_le₀ h1), by positivity, by ring, ?_⟩
  rw [smul_add, smul_smul, inv_mul_cancel₀ hs0.ne']
  module

/-! ## The frontier of a tile is covered by facets -/

/-- Every frontier point of a tile lies on a facet with another tile. -/
theorem IsSiteSystem.exists_facet_of_mem_frontier (hV : IsSiteSystem V r) {p f : Plane} (hp : p ∈ V)
    (hf : f ∈ frontier (tile V p)) : ∃ q ∈ V, q ≠ p ∧ f ∈ facet V p q := by
  by_contra hcon
  push Not at hcon
  set R := r p / 99 + 1 with hR
  have hft : f ∈ tile V p := (isClosed_tile V p).frontier_subset hf
  have hrp := hV.pos p
  have hfR : dist f p < R := by
    have := hV.dist_le hft
    rw [hR]
    linarith
  have hfin : (nearSites V p R).Finite := (hV.finite p (2 * R)).subset fun q hq => hq
  have hev : ∀ᶠ y in 𝓝 f, dist y p < R ∧
      ∀ q ∈ nearSites V p R, q ≠ p → 0 < bisector p q y := by
    refine Filter.Eventually.and ?_ ((Filter.eventually_all_finite hfin).2 fun q hq => ?_)
    · have hc : Continuous fun y : Plane => dist y p := by fun_prop
      exact hc.continuousAt.eventually_lt continuousAt_const hfR
    · by_cases hqp : q = p
      · exact Filter.Eventually.of_forall fun y h => absurd hqp h
      · have hpos : 0 < bisector p q f := lt_of_le_of_ne
          ((dist_le_dist_iff_bisector p q f).1 (hft q hq.1)) fun h =>
            hcon q hq.1 hqp ((mem_facet_iff_bisector hp hq.1).2 ⟨hft, h.symm⟩)
        have hc : Continuous fun y : Plane => bisector p q y := by unfold bisector; fun_prop
        exact ((hc.tendsto f).eventually (lt_mem_nhds hpos)).mono fun y hy _ => hy
  have hint : f ∈ interior (tile V p) := mem_interior_iff_mem_nhds.2 (hev.mono fun y hy =>
    mem_tile_of_nearSites hy.1.le fun q hq => by
      by_cases hqp : q = p
      · subst hqp
        exact le_rfl
      · exact (dist_le_dist_iff_bisector p q y).2 (hy.2 q hq hqp).le)
  exact hf.2 hint

/-! ## The fan triangles -/

/-- **Pairs of sites with a nondegenerate facet**: the tile of `q` meets the tile of `p` in more
than one point, hence in an edge of the polygon `Q_p`. -/
def IsFanPair (V : Set Plane) (p q : Plane) : Prop :=
  p ∈ V ∧ q ∈ V ∧ p ≠ q ∧ (facet V p q).Nontrivial

theorem IsFanPair.symm {p q : Plane} (h : IsFanPair V p q) : IsFanPair V q p :=
  ⟨h.2.1, h.1, h.2.2.1.symm, by rw [facet_comm]; exact h.2.2.2⟩

/-- **The fan triangle** of a nondegenerate facet: the convex hull of the site and the facet. -/
def fan (V : Set Plane) (p q : Plane) : Set Plane := convexHull ℝ (insert p (facet V p q))

/-- **The vertices of the fan triangle**: the site and the endpoints of the facet. -/
def fanVerts (V : Set Plane) (p q : Plane) : Set Plane := insert p ((facet V p q).extremePoints ℝ)

theorem convex_fan (V : Set Plane) (p q : Plane) : Convex ℝ (fan V p q) := convex_convexHull ℝ _

theorem self_mem_fan (V : Set Plane) (p q : Plane) : p ∈ fan V p q :=
  subset_convexHull ℝ _ (mem_insert _ _)

theorem facet_subset_fan (V : Set Plane) (p q : Plane) : facet V p q ⊆ fan V p q := fun _ hx =>
  subset_convexHull ℝ _ (mem_insert_of_mem _ hx)

theorem segment_subset_fan (V : Set Plane) (p q : Plane) {f : Plane} (hf : f ∈ facet V p q) :
    segment ℝ p f ⊆ fan V p q :=
  (convex_fan V p q).segment_subset (self_mem_fan V p q) (facet_subset_fan V p q hf)

theorem fan_subset_tile (V : Set Plane) (p q : Plane) : fan V p q ⊆ tile V p :=
  convexHull_min (insert_subset (self_mem_tile V p) (facet_subset_left V p q)) (convex_tile V p)

theorem exists_ne_zero_plane : ∃ u : Plane, u ≠ 0 :=
  ⟨EuclideanSpace.single 0 1, fun h => by simpa using congrArg (fun x : Plane => x 0) h⟩

/-- **Every frontier point of a tile lies on a nondegenerate facet** (answer, line 23: the boundary
of the tile is the union of its edges). The frontier is a connected set without isolated points, and
the finitely many degenerate facets are isolated points. -/
theorem IsSiteSystem.frontier_tile_subset_facets (hV : IsSiteSystem V r) {p : Plane} (hp : p ∈ V) :
    frontier (tile V p) ⊆ ⋃ q ∈ {q | IsFanPair V p q}, facet V p q := by
  set R := r p / 99 + 1 with hR
  have hfin : (nearSites V p R).Finite := (hV.finite p (2 * R)).subset fun q hq => hq
  set Qn : Set Plane := {q ∈ nearSites V p R | q ≠ p ∧ (facet V p q).Nontrivial} with hQn
  set Qd : Set Plane := {q ∈ nearSites V p R | q ≠ p ∧ ¬ (facet V p q).Nontrivial} with hQd
  set D : Set Plane := ⋃ q ∈ Qn, facet V p q with hD
  set E : Set Plane := ⋃ q ∈ Qd, facet V p q with hE
  have hDclosed : IsClosed D :=
    (hfin.subset fun q hq => hq.1).isClosed_biUnion fun q _ => (hV.isCompact_facet p q).isClosed
  have hEfin : E.Finite := (hfin.subset fun q hq => hq.1).biUnion fun q hq =>
    (Set.not_nontrivial_iff.1 hq.2.2).finite
  have hcover : ∀ z ∈ frontier (tile V p), z ∈ D ∪ E := by
    intro z hz
    obtain ⟨q, hqV, hqp, hzq⟩ := hV.exists_facet_of_mem_frontier hp hz
    have hqN := hV.mem_nearSites_of_mem_facet hp hqV hzq
    by_cases hnt : (facet V p q).Nontrivial
    · exact Or.inl (mem_iUnion₂.2 ⟨q, ⟨hqN, hqp, hnt⟩, hzq⟩)
    · exact Or.inr (mem_iUnion₂.2 ⟨q, ⟨hqN, hqp, hnt⟩, hzq⟩)
  have hnt : (frontier (tile V p)).Nontrivial := by
    obtain ⟨u, hu⟩ := exists_ne_zero_plane
    obtain ⟨s, hs0, hsf, -⟩ := hV.exists_exit p hu
    obtain ⟨s', hs0', hsf', -⟩ := hV.exists_exit p (neg_ne_zero.2 hu)
    refine ⟨_, hsf, _, hsf', fun h => ?_⟩
    have h1 := add_left_cancel h
    rw [smul_neg] at h1
    have h2 : (s + s') • u = 0 := by rw [add_smul, h1]; abel
    exact hu ((smul_eq_zero.1 h2).resolve_left (by positivity))
  intro y hy
  by_contra hyD'
  have hyD : y ∉ D := fun h => by
    obtain ⟨q, hq, hyq⟩ := mem_iUnion₂.1 h
    exact hyD' (mem_iUnion₂.2 ⟨q, ⟨hp, hq.1.1, Ne.symm hq.2.1, hq.2.2⟩, hyq⟩)
  have hyE : y ∈ E := (hcover y hy).resolve_left hyD
  have hperf := (hV.isConnected_frontier_tile p).isPreconnected.preperfect_of_nontrivial hnt y hy
  have hW : (D ∪ (E \ {y}))ᶜ ∈ 𝓝 y := by
    refine IsOpen.mem_nhds (hDclosed.union hEfin.sdiff.isClosed).isOpen_compl ?_
    rintro (h | h)
    · exact hyD h
    · exact h.2 rfl
  obtain ⟨z, ⟨hzy, hzF⟩, hzW⟩ := ((accPt_iff_frequently.1 hperf).and_eventually hW).exists
  rcases hcover z hzF with h | h
  · exact hzW (Or.inl h)
  · exact hzW (Or.inr ⟨h, hzy⟩)

theorem IsSiteSystem.exists_isFanPair (hV : IsSiteSystem V r) {p : Plane} (hp : p ∈ V) :
    ∃ q, IsFanPair V p q := by
  obtain ⟨u, hu⟩ := exists_ne_zero_plane
  obtain ⟨s, -, hsf, -⟩ := hV.exists_exit p hu
  obtain ⟨q, hq, -⟩ := mem_iUnion₂.1 (hV.frontier_tile_subset_facets hp hsf)
  exact ⟨q, hq⟩

/-- **The tile is the union of its fan triangles**: it is star-shaped from `p`, and every frontier
point lies on a nondegenerate facet. -/
theorem IsSiteSystem.tile_eq_iUnion_fan (hV : IsSiteSystem V r) {p : Plane} (hp : p ∈ V) :
    tile V p = ⋃ q ∈ {q | IsFanPair V p q}, fan V p q := by
  refine Subset.antisymm (fun x hx => ?_) (iUnion₂_subset fun q _ => fan_subset_tile V p q)
  by_cases hxp : x = p
  · obtain ⟨q, hq⟩ := hV.exists_isFanPair hp
    exact mem_iUnion₂.2 ⟨q, hq, hxp ▸ self_mem_fan V p q⟩
  · obtain ⟨f, hf, hxf⟩ := hV.exists_frontier_of_mem_tile hx hxp
    obtain ⟨q, hq, hfq⟩ := mem_iUnion₂.1 (hV.frontier_tile_subset_facets hp hf)
    exact mem_iUnion₂.2 ⟨q, hq, segment_subset_fan V p q hfq hxf⟩

/-- **Local finiteness**: only finitely many fan triangles meet a compact set. -/
theorem IsSiteSystem.finite_fanPairs_meeting (hV : IsSiteSystem V r) {A : Set Plane}
    (hA : IsCompact A) :
    {pq : Plane × Plane | IsFanPair V pq.1 pq.2 ∧ (fan V pq.1 pq.2 ∩ A).Nonempty}.Finite := by
  obtain ⟨R₀, hR₀⟩ := hA.isBounded.subset_closedBall (0 : Plane)
  have hP : {p ∈ V | (tile V p ∩ closedBall 0 R₀).Nonempty}.Finite := hV.finite_tiles_meeting 0 R₀
  refine (hP.biUnion fun p _ =>
    ((hV.finite p (2 * (r p / 99 + 1))).image (Prod.mk p))).subset ?_
  rintro ⟨p, q⟩ ⟨hpq, y, hyfan, hyA⟩
  refine mem_iUnion₂.2 ⟨p, ⟨hpq.1, y, fan_subset_tile V p q hyfan, hR₀ hyA⟩, ?_⟩
  obtain ⟨z, hz⟩ := hpq.2.2.2.nonempty
  exact ⟨q, hV.mem_nearSites_of_mem_facet hpq.1 hpq.2.1 hz, rfl⟩

/-! ## Faces of the tiles -/

theorem bisector_combo (p q x y : Plane) {a b : ℝ} (hab : a + b = 1) :
    bisector p q (a • x + b • y) = a * bisector p q x + b * bisector p q y := by
  unfold bisector
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  linear_combination (-(‖q‖ ^ 2 - ‖p‖ ^ 2)) * hab

/-- **A facet is a face of its tile.** -/
theorem isExtreme_facet {p q : Plane} (hp : p ∈ V) (hq : q ∈ V) :
    IsExtreme ℝ (tile V p) (facet V p q) := by
  refine ⟨facet_subset_left V p q, fun x hx y hy z hz hzs => ?_⟩
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hzs
  have hgz : bisector p q (a • x + b • y) = 0 := ((mem_facet_iff_bisector hp hq).1 hz).2
  have hgx : 0 ≤ bisector p q x := (dist_le_dist_iff_bisector p q x).1 (hx q hq)
  have hgy : 0 ≤ bisector p q y := (dist_le_dist_iff_bisector p q y).1 (hy q hq)
  rw [bisector_combo p q x y hab] at hgz
  have hx0 : bisector p q x = 0 := by
    refine le_antisymm ?_ hgx
    by_contra h
    push Not at h
    nlinarith [mul_pos ha h, mul_nonneg hb.le hgy]
  exact (mem_facet_iff_bisector hp hq).2 ⟨hx, hx0⟩

theorem extremePoints_facet {p q : Plane} (hp : p ∈ V) (hq : q ∈ V) :
    (facet V p q).extremePoints ℝ = facet V p q ∩ tileVertices V p :=
  (isExtreme_facet hp hq).extremePoints_eq

/-- Two distinct facets of a tile meet in at most one point. -/
theorem facet_inter_facet_subsingleton {p q₁ q₂ : Plane} (hp : p ∈ V) (hq₁ : q₁ ∈ V) (hq₂ : q₂ ∈ V)
    (h₁ : q₁ ≠ p) (h₂ : q₂ ≠ p) (h₁₂ : q₁ ≠ q₂) :
    (facet V p q₁ ∩ facet V p q₂).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  have hx1 := ((mem_facet_iff hp hq₁).1 hx.1).2
  have hx2 := ((mem_facet_iff hp hq₂).1 hx.2).2
  have hy1 := ((mem_facet_iff hp hq₁).1 hy.1).2
  have hy2 := ((mem_facet_iff hp hq₂).1 hy.2).2
  rw [dist_comm x p, dist_comm x q₁] at hx1
  rw [dist_comm x p, dist_comm x q₂] at hx2
  rw [dist_comm y p, dist_comm y q₁] at hy1
  rw [dist_comm y p, dist_comm y q₂] at hy2
  have := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2)) hxy h₁.symm rfl hx1.symm hx2.symm rfl hy1.symm
    hy2.symm
  rcases this with h | h
  · exact h₂ h
  · exact h₁₂ h.symm

/-- **A point on two distinct facets of a tile is a vertex of the tile.** -/
theorem mem_tileVertices_of_mem_facet_inter {p q₁ q₂ x : Plane} (hp : p ∈ V) (hq₁ : q₁ ∈ V)
    (hq₂ : q₂ ∈ V) (h₁ : q₁ ≠ p) (h₂ : q₂ ≠ p) (h₁₂ : q₁ ≠ q₂) (hx₁ : x ∈ facet V p q₁)
    (hx₂ : x ∈ facet V p q₂) : x ∈ tileVertices V p := by
  refine ⟨hx₁.1, fun y hy z hz hxyz => ?_⟩
  have h1 : y ∈ facet V p q₁ :=
    (isExtreme_facet hp hq₁).left_mem_of_mem_openSegment hy hz hx₁ hxyz
  have h2 : y ∈ facet V p q₂ :=
    (isExtreme_facet hp hq₂).left_mem_of_mem_openSegment hy hz hx₂ hxyz
  exact facet_inter_facet_subsingleton hp hq₁ hq₂ h₁ h₂ h₁₂ ⟨h1, h2⟩ ⟨hx₁, hx₂⟩

/-- **The endpoints of a facet span it.** -/
theorem IsSiteSystem.convexHull_extremePoints_facet (hV : IsSiteSystem V r) {p q : Plane}
    (hp : p ∈ V) (hq : q ∈ V) : convexHull ℝ ((facet V p q).extremePoints ℝ) = facet V p q := by
  have hfin : ((facet V p q).extremePoints ℝ).Finite := by
    rw [extremePoints_facet hp hq]
    exact (hV.finite_tileVertices p).subset inter_subset_right
  have hclosed : IsClosed (convexHull ℝ ((facet V p q).extremePoints ℝ)) :=
    (Set.Finite.isCompact_convexHull (𝕜 := ℝ) hfin).isClosed
  have := closure_convexHull_extremePoints (hV.isCompact_facet p q) (convex_facet V p q)
  rwa [hclosed.closure_eq] at this

theorem fanVerts_subset_fan (V : Set Plane) (p q : Plane) : fanVerts V p q ⊆ fan V p q :=
  insert_subset_iff.2
    ⟨self_mem_fan V p q, fun _ hx => facet_subset_fan V p q (extremePoints_subset hx)⟩

/-- **The fan triangle is the convex hull of its vertices.** -/
theorem IsSiteSystem.fan_eq_convexHull_fanVerts (hV : IsSiteSystem V r) {p q : Plane} (hp : p ∈ V)
    (hq : q ∈ V) : fan V p q = convexHull ℝ (fanVerts V p q) := by
  apply Subset.antisymm
  · refine convexHull_min (insert_subset (subset_convexHull ℝ _ (mem_insert _ _)) ?_)
      (convex_convexHull ℝ _)
    rw [← hV.convexHull_extremePoints_facet hp hq]
    exact convexHull_mono (subset_insert _ _)
  · exact convexHull_min (fanVerts_subset_fan V p q) (convex_fan V p q)

/-! ## Intersections of fan triangles -/

theorem exists_mem_segment_of_mem_fan {p q x : Plane} (hF : (facet V p q).Nonempty)
    (hx : x ∈ fan V p q) : ∃ f ∈ facet V p q, x ∈ segment ℝ p f := by
  unfold fan at hx
  rw [convexHull_insert hF, (convex_facet V p q).convexHull_eq, mem_convexJoin] at hx
  obtain ⟨a, ha, b, hb, hxab⟩ := hx
  rw [mem_singleton_iff.1 ha] at hxab
  exact ⟨b, hb, hxab⟩

theorem exists_eq_add_smul_of_mem_segment {p f x : Plane} (hx : x ∈ segment ℝ p f) (hxp : x ≠ p) :
    ∃ s : ℝ, 0 < s ∧ f = p + s • (x - p) := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
  have hb0 : b ≠ 0 := by
    rintro rfl
    have : a = 1 := by linarith
    subst this
    simp at hxp
  refine ⟨b⁻¹, by positivity, ?_⟩
  have h1 : a • p + b • f - p = b • (f - p) := by
    have : a = 1 - b := by linarith
    subst this
    module
  rw [h1, smul_smul, inv_mul_cancel₀ hb0, one_smul]
  abel

theorem mem_segment_of_smul {p f f' u : Plane} {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s')
    (hf : f = p + s • u) (hf' : f' = p + s' • u) : f ∈ segment ℝ p f' := by
  have hs' : 0 < s' := lt_of_lt_of_le hs hss
  refine ⟨1 - s / s', s / s', sub_nonneg.2 ((div_le_one hs').2 hss), by positivity, by ring, ?_⟩
  rw [hf, hf', smul_add, smul_smul, div_mul_cancel₀ _ hs'.ne']
  module

/-- **Rays leave a tile once**: two frontier points on a segment from the site through `x`
coincide. -/
theorem IsSiteSystem.eq_of_mem_segment_of_mem_segment (hV : IsSiteSystem V r) (p : Plane)
    {x f f' : Plane} (hxp : x ≠ p) (hf : f ∈ frontier (tile V p)) (hf' : f' ∈ frontier (tile V p))
    (hx : x ∈ segment ℝ p f) (hx' : x ∈ segment ℝ p f') : f = f' := by
  obtain ⟨s, hs, hfs⟩ := exists_eq_add_smul_of_mem_segment hx hxp
  obtain ⟨s', hs', hfs'⟩ := exists_eq_add_smul_of_mem_segment hx' hxp
  rcases le_total s s' with h | h
  · exact hV.eq_of_mem_segment_of_mem_frontier p ((isClosed_tile V p).frontier_subset hf')
      (mem_segment_of_smul hs h hfs hfs') hf
  · exact (hV.eq_of_mem_segment_of_mem_frontier p ((isClosed_tile V p).frontier_subset hf)
      (mem_segment_of_smul hs' h hfs' hfs) hf').symm

theorem fanVerts_inter_subset_fan (V : Set Plane) (p q p' q' : Plane) :
    fanVerts V p q ∩ fanVerts V p' q' ⊆ fan V p q ∩ fan V p' q' := fun _ hx =>
  ⟨fanVerts_subset_fan V p q hx.1, fanVerts_subset_fan V p' q' hx.2⟩

/-- Two fan triangles of the same tile meet in the convex hull of their common vertices. -/
theorem IsSiteSystem.fan_inter_fan_same (hV : IsSiteSystem V r) {p q q' : Plane}
    (h : IsFanPair V p q) (h' : IsFanPair V p q') (hqq : q ≠ q') :
    fan V p q ∩ fan V p q' = convexHull ℝ (fanVerts V p q ∩ fanVerts V p q') := by
  refine Subset.antisymm ?_ (convexHull_min (fanVerts_inter_subset_fan V p q p q')
    ((convex_fan V p q).inter (convex_fan V p q')))
  rintro x ⟨hx, hx'⟩
  by_cases hxp : x = p
  · exact subset_convexHull ℝ _ ⟨hxp ▸ mem_insert _ _, hxp ▸ mem_insert _ _⟩
  · obtain ⟨f, hf, hxf⟩ := exists_mem_segment_of_mem_fan h.2.2.2.nonempty hx
    obtain ⟨f', hf', hxf'⟩ := exists_mem_segment_of_mem_fan h'.2.2.2.nonempty hx'
    have hff : f = f' := hV.eq_of_mem_segment_of_mem_segment p hxp
      (facet_subset_frontier h.1 h.2.1 h.2.2.1 hf) (facet_subset_frontier h'.1 h'.2.1 h'.2.2.1 hf')
      hxf hxf'
    subst hff
    have hv : f ∈ tileVertices V p := mem_tileVertices_of_mem_facet_inter h.1 h.2.1 h'.2.1
      h.2.2.1.symm h'.2.2.1.symm hqq hf hf'
    have e1 : f ∈ fanVerts V p q :=
      mem_insert_of_mem _ (by rw [extremePoints_facet h.1 h.2.1]; exact ⟨hf, hv⟩)
    have e2 : f ∈ fanVerts V p q' :=
      mem_insert_of_mem _ (by rw [extremePoints_facet h'.1 h'.2.1]; exact ⟨hf', hv⟩)
    exact (convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ (fanVerts V p q ∩ fanVerts V p q') ⟨mem_insert _ _, mem_insert _ _⟩)
      (subset_convexHull ℝ (fanVerts V p q ∩ fanVerts V p q') ⟨e1, e2⟩) hxf

/-- The vertices of two adjacent facets: a point of two facets of the tile of `p` with `q ≠ p'` is
an endpoint of both. -/
theorem mem_extremePoints_facet_of_mem_facet_inter {p q p' x : Plane} (hp : p ∈ V) (hq : q ∈ V)
    (hp' : p' ∈ V) (hqp : q ≠ p) (hp'p : p' ≠ p) (hqp' : q ≠ p') (hxq : x ∈ facet V p q)
    (hxp' : x ∈ facet V p p') :
    x ∈ (facet V p q).extremePoints ℝ ∧ x ∈ (facet V p p').extremePoints ℝ := by
  have hv := mem_tileVertices_of_mem_facet_inter hp hq hp' hqp hp'p hqp' hxq hxp'
  rw [extremePoints_facet hp hq, extremePoints_facet hp hp']
  exact ⟨⟨hxq, hv⟩, ⟨hxp', hv⟩⟩

/-- Two fan triangles of different tiles meet in the convex hull of their common vertices. -/
theorem IsSiteSystem.fan_inter_fan_ne (hV : IsSiteSystem V r) {p q p' q' : Plane}
    (h : IsFanPair V p q) (h' : IsFanPair V p' q') (hpp : p ≠ p') :
    fan V p q ∩ fan V p' q' = convexHull ℝ (fanVerts V p q ∩ fanVerts V p' q') := by
  refine Subset.antisymm ?_ (convexHull_min (fanVerts_inter_subset_fan V p q p' q')
    ((convex_fan V p q).inter (convex_fan V p' q')))
  rintro x ⟨hx, hx'⟩
  have hxG : x ∈ facet V p p' := ⟨fan_subset_tile V p q hx, fan_subset_tile V p' q' hx'⟩
  have hxG' : x ∈ facet V p' p := by rwa [facet_comm] at hxG
  have hxfr : x ∈ frontier (tile V p) := facet_subset_frontier h.1 h'.1 hpp hxG
  have hxfr' : x ∈ frontier (tile V p') := facet_subset_frontier h'.1 h.1 hpp.symm hxG'
  have hxq : x ∈ facet V p q := by
    obtain ⟨f, hf, hxf⟩ := exists_mem_segment_of_mem_fan h.2.2.2.nonempty hx
    rwa [hV.eq_of_mem_segment_of_mem_frontier p (facet_subset_left V p q hf) hxf hxfr]
  have hxq' : x ∈ facet V p' q' := by
    obtain ⟨f, hf, hxf⟩ := exists_mem_segment_of_mem_fan h'.2.2.2.nonempty hx'
    rwa [hV.eq_of_mem_segment_of_mem_frontier p' (facet_subset_left V p' q' hf) hxf hxfr']
  by_cases c1 : q = p'
  · by_cases c2 : q' = p
    · have hG := hV.convexHull_extremePoints_facet h.1 h'.1
      have hsub : (facet V p p').extremePoints ℝ ⊆ fanVerts V p q ∩ fanVerts V p' q' := fun y hy =>
        ⟨by rw [c1]; exact mem_insert_of_mem _ hy,
          by
            rw [c2]
            show y ∈ insert p' ((facet V p' p).extremePoints ℝ)
            rw [facet_comm]
            exact mem_insert_of_mem _ hy⟩
      have : convexHull ℝ ((facet V p p').extremePoints ℝ) ⊆
          convexHull ℝ (fanVerts V p q ∩ fanVerts V p' q') := convexHull_mono hsub
      rw [hG] at this
      exact this hxG
    · obtain ⟨E2, E1'⟩ := mem_extremePoints_facet_of_mem_facet_inter h'.1 h'.2.1 h.1 h'.2.2.1.symm
        hpp c2 hxq' hxG'
      have E1 : x ∈ (facet V p q).extremePoints ℝ := by rw [c1, facet_comm]; exact E1'
      exact subset_convexHull ℝ (fanVerts V p q ∩ fanVerts V p' q')
        ⟨mem_insert_of_mem _ E1, mem_insert_of_mem _ E2⟩
  · obtain ⟨E1, Ep'⟩ := mem_extremePoints_facet_of_mem_facet_inter h.1 h.2.1 h'.1 h.2.2.1.symm
      hpp.symm c1 hxq hxG
    have E2 : x ∈ (facet V p' q').extremePoints ℝ := by
      by_cases c2 : q' = p
      · rw [c2, facet_comm]; exact Ep'
      · exact (mem_extremePoints_facet_of_mem_facet_inter h'.1 h'.2.1 h.1 h'.2.2.1.symm hpp
          c2 hxq' hxG').1
    exact subset_convexHull ℝ (fanVerts V p q ∩ fanVerts V p' q')
      ⟨mem_insert_of_mem _ E1, mem_insert_of_mem _ E2⟩

/-- **Fan triangles pairwise meet in a common face**: for two different pairs the intersection of
the triangles is the convex hull of their common vertices (empty, a common vertex, or a common
edge). -/
theorem IsSiteSystem.fan_inter_fan (hV : IsSiteSystem V r) {p q p' q' : Plane}
    (h : IsFanPair V p q) (h' : IsFanPair V p' q') (hne : (p, q) ≠ (p', q')) :
    fan V p q ∩ fan V p' q' = convexHull ℝ (fanVerts V p q ∩ fanVerts V p' q') := by
  by_cases hpp : p = p'
  · subst hpp
    exact hV.fan_inter_fan_same h h' fun hqq => hne (by rw [hqq])
  · exact hV.fan_inter_fan_ne h h' hpp

/-! ## The edges of the fan triangles -/

/-- **The frontier of a tile is the union of its facets.** -/
theorem IsSiteSystem.frontier_tile_eq_iUnion_facet (hV : IsSiteSystem V r) {p : Plane}
    (hp : p ∈ V) :
    frontier (tile V p) = ⋃ q ∈ {q | IsFanPair V p q}, facet V p q :=
  Subset.antisymm (hV.frontier_tile_subset_facets hp)
    (iUnion₂_subset fun _ hq => facet_subset_frontier hp hq.2.1 hq.2.2.1)

/-- **Every vertex of a tile is an endpoint of a facet.** -/
theorem IsSiteSystem.tileVertices_subset_extremePoints_facet (hV : IsSiteSystem V r) {p v : Plane}
    (hp : p ∈ V) (hv : v ∈ tileVertices V p) :
    ∃ q, IsFanPair V p q ∧ v ∈ (facet V p q).extremePoints ℝ := by
  obtain ⟨q, hq, hvq⟩ := mem_iUnion₂.1
    (hV.frontier_tile_subset_facets hp (tileVertices_subset_frontier V p hv))
  exact ⟨q, hq, by rw [extremePoints_facet hp hq.2.1]; exact ⟨hvq, hv⟩⟩

/-- **The shared piece of a tile is a union of fan triangle edges**: the facets and the spokes
`[p, v]` to the endpoints of the facets. -/
theorem IsSiteSystem.shared_eq_iUnion_edges (hV : IsSiteSystem V r) {p : Plane} (hp : p ∈ V) :
    shared V p = ⋃ q ∈ {q | IsFanPair V p q},
      (facet V p q ∪ ⋃ v ∈ (facet V p q).extremePoints ℝ, segment ℝ p v) := by
  refine Subset.antisymm ?_ (iUnion₂_subset fun q hq => union_subset
    (fun y hy => Or.inl (facet_subset_frontier hp hq.2.1 hq.2.2.1 hy))
    (iUnion₂_subset fun v hv => ?_))
  · rintro y (hy | hy)
    · obtain ⟨q, hq, hyq⟩ := mem_iUnion₂.1 (hV.frontier_tile_subset_facets hp hy)
      exact mem_iUnion₂.2 ⟨q, hq, Or.inl hyq⟩
    · obtain ⟨v, hv, hyv⟩ := mem_iUnion₂.1 hy
      obtain ⟨q, hq, hvq⟩ := hV.tileVertices_subset_extremePoints_facet hp hv
      exact mem_iUnion₂.2 ⟨q, hq, Or.inr (mem_iUnion₂.2 ⟨v, hvq, hyv⟩)⟩
  · have hvt : v ∈ tileVertices V p := by
      rw [extremePoints_facet hp hq.2.1] at hv
      exact hv.2
    exact fun y hy => Or.inr (mem_iUnion₂.2 ⟨v, hvt, hy⟩)

namespace PolygonalInput

variable {I : PolygonalInput}

/-- **A polygonal cell is a union of fan triangles and fan triangle edges**: each tile it owns is
the union of its fan triangles, and each other tile contributes the facets and spokes of its fan
triangles. -/
theorem cell_eq_iUnion (hV : IsSiteSystem I.V I.r) (j : ℤ) :
    I.cell j = ⋃ p ∈ I.sitesOf j,
      if I.owner p = j then ⋃ q ∈ {q | IsFanPair I.V p q}, fan I.V p q
      else ⋃ q ∈ {q | IsFanPair I.V p q},
        (facet I.V p q ∪ ⋃ v ∈ (facet I.V p q).extremePoints ℝ, segment ℝ p v) := by
  unfold cell
  refine iUnion₂_congr fun p hp => ?_
  unfold piece
  split_ifs
  · exact hV.tile_eq_iUnion_fan hp.1
  · exact hV.shared_eq_iUnion_edges hp.1

end PolygonalInput

end MatedCRT.ZeroConePolygonal
