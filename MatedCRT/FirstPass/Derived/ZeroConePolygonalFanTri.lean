import MatedCRT.FirstPass.Derived.ZeroConePolygonalFan
import MatedCRT.FirstPass.Derived.ZeroConePolygonalPL

/-!
# The fan triangulation as a triangulation of the plane

The Borel measurability of the polygonal cell configuration compares two configurations through a
homeomorphism of the plane carrying cells to cells and moving points little, as in the topology of
cell configurations of Gwynne–Miller–Sheffield (arXiv:1807.07515v3, (1.14)–(1.15), p. 15). The
homeomorphism is the affine interpolation of slightly displaced vertices on the triangles of a
triangulation in which every cell is a union of faces. This file shows that the fan triangles of
the Voronoi tiles (`fan V p q`, the convex hull of the site `p` and a nondegenerate facet
`Q_p ∩ Q_q`) form such a triangulation of the whole plane, in the form required by the gluing
lemmas (`IsTriangulation`).

* `IsSiteSystem.exists_facet_ends`: a nondegenerate facet has exactly two extreme points `a ≠ b`.
* `FanIndex V`, `facetEnds`, `fanTri V i = ![p, a, b]`: the fan triangles indexed by the pairs of
  sites with a nondegenerate facet, with their vertices.
* `IsSiteSystem.cross_fanTri_ne_zero`: the fan triangles are nondegenerate.
* `IsSiteSystem.isTriangulation_fanTri`: they form a locally finite triangulation of the plane, two
  distinct triangles meeting in the convex hull of their common vertices.
* `IsSiteSystem.tile_eq_iUnion_tri`, `IsSiteSystem.shared_eq_iUnion_fanEdges`,
  `PolygonalInput.cell_eq_iUnion_fanTri`: each tile is the union of its fan triangles, its shared
  piece is the union of their edges, and each polygonal cell is a union of fan triangles and fan
  triangle edges.
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open ReflectedGMS

variable {V : Set Plane} {r : Plane → ℝ}

/-! ## Two bisectors through a point -/

theorem cross_perp (u w : Plane) : cross u (perp w) = ⟪u, w⟫ := by
  unfold cross
  rw [perp_apply_zero, perp_apply_one, inner_eq_coord]
  ring

/-- A point `a` on the bisector of `p` and `q` satisfies `2 ⟪q - p, a - p⟫ = |q - p|²`. -/
theorem two_mul_inner_sub_eq_of_bisector {p q a : Plane} (ha : bisector p q a = 0) :
    2 * ⟪q - p, a - p⟫ = ‖q - p‖ ^ 2 := by
  unfold bisector at ha
  rw [norm_sub_sq_real]
  simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq] at ha ⊢
  have h1 := real_inner_comm a q
  have h2 := real_inner_comm a p
  linarith

/-- Two points `a, b` of the bisector of distinct sites `p, q` with `a - p` and `b - p` parallel
coincide: the site `p` is not on the bisector. -/
theorem eq_of_bisector_of_cross {p q a b : Plane} (hpq : p ≠ q) (ha : bisector p q a = 0)
    (hb : bisector p q b = 0) (hc : cross (a - p) (b - p) = 0) : a = b := by
  have hn : cross (q - p) (perp (a - p)) ≠ 0 := by
    rw [cross_perp]
    intro h0
    have h1 := two_mul_inner_sub_eq_of_bisector ha
    rw [h0, mul_zero] at h1
    have h2 : ‖q - p‖ ^ 2 = 0 := h1.symm
    exact sub_ne_zero.2 hpq.symm (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2))
  refine eq_of_cross_ne_zero hn ?_ ?_
  · unfold bisector at ha hb
    rw [inner_sub_left]
    linarith
  · rw [inner_perp]
    unfold cross at hc
    simp only [PiLp.sub_apply] at hc ⊢
    linear_combination -hc

/-! ## The ends of a facet -/

/-- **A nondegenerate facet is a segment with two distinct ends**: its extreme points are exactly
two distinct points. The facet lies on the bisector of `p` and `q`, along which the coordinate
`⟪·, (q - p)^⊥⟫` is injective; its minimum and maximum on the facet are the ends. -/
theorem IsSiteSystem.exists_facet_ends (hV : IsSiteSystem V r) {p q : Plane}
    (h : IsFanPair V p q) :
    ∃ a b : Plane, a ≠ b ∧ (facet V p q).extremePoints ℝ = {a, b} := by
  obtain ⟨hp, hq, hpq, hnt⟩ := h
  have hL : ∀ y ∈ facet V p q, bisector p q y = 0 := fun y hy =>
    ((mem_facet_iff_bisector hp hq).1 hy).2
  have hinj : ∀ y ∈ facet V p q, ∀ y' ∈ facet V p q,
      ⟪y, perp (q - p)⟫ = ⟪y', perp (q - p)⟫ → y = y' := by
    intro y hy y' hy' h
    refine eq_of_cross_ne_zero (u := q - p) (w := perp (q - p)) ?_ ?_ ?_
    · rw [cross_perp, real_inner_self_eq_norm_sq]
      exact pow_ne_zero 2 (norm_ne_zero_iff.2 (sub_ne_zero.2 hpq.symm))
    · have h1 := hL y hy
      have h2 := hL y' hy'
      unfold bisector at h1 h2
      rw [inner_sub_left]
      linarith
    · rw [inner_sub_left, h, sub_self]
  have hφ : Continuous fun y : Plane => ⟪y, perp (q - p)⟫ :=
    continuous_id.inner continuous_const
  have hcpt := hV.isCompact_facet p q
  obtain ⟨a, ha, hamin⟩ := hcpt.exists_isMinOn hnt.nonempty hφ.continuousOn
  obtain ⟨b, hb, hbmax⟩ := hcpt.exists_isMaxOn hnt.nonempty hφ.continuousOn
  rw [isMinOn_iff] at hamin
  rw [isMaxOn_iff] at hbmax
  have hab : a ≠ b := by
    rintro rfl
    obtain ⟨x, hx, y, hy, hxy⟩ := hnt
    exact hxy (hinj x hx y hy ((le_antisymm (hbmax x hx) (hamin x hx)).trans
      (le_antisymm (hbmax y hy) (hamin y hy)).symm))
  have hmin_eq : ∀ x ∈ facet V p q, ⟪x, perp (q - p)⟫ ≤ ⟪a, perp (q - p)⟫ → x = a :=
    fun x hx hle => hinj x hx a ha (le_antisymm hle (hamin x hx))
  have hmax_eq : ∀ x ∈ facet V p q, ⟪b, perp (q - p)⟫ ≤ ⟪x, perp (q - p)⟫ → x = b :=
    fun x hx hle => hinj x hx b hb (le_antisymm (hbmax x hx) hle)
  have hea : a ∈ (facet V p q).extremePoints ℝ := by
    refine ⟨ha, fun x₁ hx₁ x₂ hx₂ hx => ?_⟩
    obtain ⟨c, d, hc, hd, hcd, hxa⟩ := hx
    refine hmin_eq x₁ hx₁ ?_
    have e : c * ⟪x₁, perp (q - p)⟫ + d * ⟪x₂, perp (q - p)⟫ = ⟪a, perp (q - p)⟫ := by
      rw [← hxa, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    have h2 := hamin x₂ hx₂
    have h3 : c * ⟪a, perp (q - p)⟫ + d * ⟪a, perp (q - p)⟫ = ⟪a, perp (q - p)⟫ := by
      rw [← add_mul, hcd, one_mul]
    by_contra hlt
    have hlt' := not_le.1 hlt
    nlinarith [mul_pos hc (sub_pos.2 hlt'), mul_nonneg hd.le (sub_nonneg.2 h2)]
  have heb : b ∈ (facet V p q).extremePoints ℝ := by
    refine ⟨hb, fun x₁ hx₁ x₂ hx₂ hx => ?_⟩
    obtain ⟨c, d, hc, hd, hcd, hxb⟩ := hx
    refine hmax_eq x₁ hx₁ ?_
    have e : c * ⟪x₁, perp (q - p)⟫ + d * ⟪x₂, perp (q - p)⟫ = ⟪b, perp (q - p)⟫ := by
      rw [← hxb, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    have h2 := hbmax x₂ hx₂
    have h3 : c * ⟪b, perp (q - p)⟫ + d * ⟪b, perp (q - p)⟫ = ⟪b, perp (q - p)⟫ := by
      rw [← add_mul, hcd, one_mul]
    by_contra hlt
    have hlt' := not_le.1 hlt
    nlinarith [mul_pos hc (sub_pos.2 hlt'), mul_nonneg hd.le (sub_nonneg.2 h2)]
  have hseg : facet V p q ⊆ segment ℝ a b := by
    intro y hy
    have hya := hamin y hy
    have hyb := hbmax y hy
    have hlt : ⟪a, perp (q - p)⟫ < ⟪b, perp (q - p)⟫ :=
      lt_of_le_of_ne (hamin b hb) fun h => hab (hinj a ha b hb h)
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (⟪y, perp (q - p)⟫ - ⟪a, perp (q - p)⟫) /
        (⟪b, perp (q - p)⟫ - ⟪a, perp (q - p)⟫) := ⟨_, rfl⟩
    have hden : ⟪b, perp (q - p)⟫ - ⟪a, perp (q - p)⟫ ≠ 0 := (sub_pos.2 hlt).ne'
    have hkey : t * (⟪b, perp (q - p)⟫ - ⟪a, perp (q - p)⟫) =
        ⟪y, perp (q - p)⟫ - ⟪a, perp (q - p)⟫ := by
      rw [ht]
      exact div_mul_cancel₀ _ hden
    have ht0 : 0 ≤ t := by
      rw [ht]
      exact div_nonneg (sub_nonneg.2 hya) (sub_pos.2 hlt).le
    have ht1 : t ≤ 1 := by
      rw [ht]
      exact (div_le_one₀ (sub_pos.2 hlt)).2 (by linarith)
    have hz : (1 - t) • a + t • b ∈ facet V p q :=
      convex_facet V p q ha hb (by linarith) ht0 (by ring)
    refine ⟨1 - t, t, by linarith, ht0, by ring, hinj _ hz y hy ?_⟩
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    linear_combination hkey
  refine ⟨a, b, hab, Subset.antisymm (fun e he => ?_)
    (insert_subset hea (singleton_subset_iff.2 heb))⟩
  have hes := hseg he.1
  by_contra hne
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hne
  exact hne.1 (he.2 ha hb
    (mem_openSegment_of_ne_left_right (Ne.symm hne.1) (Ne.symm hne.2) hes)).symm

/-! ## The fan triangles with their vertices -/

/-- **The index set of the fan triangulation**: the pairs of sites `(p, q)` with a nondegenerate
facet. -/
abbrev FanIndex (V : Set Plane) : Type := {pq : Plane × Plane // IsFanPair V pq.1 pq.2}

open Classical in
/-- **The two ends of the facet** `Q_p ∩ Q_q` (in an arbitrary order; `(p, p)` if the facet is not a
segment with two distinct ends). -/
def facetEnds (V : Set Plane) (p q : Plane) : Plane × Plane :=
  if h : ∃ ab : Plane × Plane, ab.1 ≠ ab.2 ∧ (facet V p q).extremePoints ℝ = {ab.1, ab.2} then
    h.choose
  else (p, p)

/-- **The vertices of the fan triangle** of `i = (p, q)`: the site `p` and the two ends of the facet
`Q_p ∩ Q_q`. -/
def fanTri (V : Set Plane) (i : FanIndex V) : Fin 3 → Plane :=
  ![i.1.1, (facetEnds V i.1.1 i.1.2).1, (facetEnds V i.1.1 i.1.2).2]

/-- The three edges of the fan triangle of `i`. -/
def fanEdges (V : Set Plane) (i : FanIndex V) : Set Plane :=
  segment ℝ (fanTri V i 1) (fanTri V i 2) ∪ segment ℝ (fanTri V i 0) (fanTri V i 1) ∪
    segment ℝ (fanTri V i 0) (fanTri V i 2)

theorem fanTri_zero (i : FanIndex V) : fanTri V i 0 = i.1.1 := rfl

theorem fanTri_one (i : FanIndex V) : fanTri V i 1 = (facetEnds V i.1.1 i.1.2).1 := rfl

theorem fanTri_two (i : FanIndex V) : fanTri V i 2 = (facetEnds V i.1.1 i.1.2).2 := rfl

theorem IsSiteSystem.facetEnds_spec (hV : IsSiteSystem V r) {p q : Plane} (h : IsFanPair V p q) :
    (facetEnds V p q).1 ≠ (facetEnds V p q).2 ∧
      (facet V p q).extremePoints ℝ = {(facetEnds V p q).1, (facetEnds V p q).2} := by
  have hex : ∃ ab : Plane × Plane, ab.1 ≠ ab.2 ∧ (facet V p q).extremePoints ℝ = {ab.1, ab.2} := by
    obtain ⟨a, b, hab, he⟩ := hV.exists_facet_ends h
    exact ⟨(a, b), hab, he⟩
  unfold facetEnds
  rw [dite_eq_left hex]
  exact hex.choose_spec

/-- The vertex set of the fan triangle of `i` (`fanVerts`) is `{p, a, b}`. -/
theorem IsSiteSystem.fanVerts_eq (hV : IsSiteSystem V r) (i : FanIndex V) :
    fanVerts V i.1.1 i.1.2 = {fanTri V i 0, fanTri V i 1, fanTri V i 2} := by
  obtain ⟨-, he⟩ := hV.facetEnds_spec i.2
  rw [fanVerts, he, fanTri_zero, fanTri_one, fanTri_two]

/-- **The fan triangle of `i` is the triangle with vertices `fanTri V i`.** -/
theorem IsSiteSystem.tri_fanTri (hV : IsSiteSystem V r) (i : FanIndex V) :
    tri (fanTri V) i = fan V i.1.1 i.1.2 := by
  rw [hV.fan_eq_convexHull_fanVerts i.2.1 i.2.2.1, hV.fanVerts_eq i]
  rfl

/-- **The facet of `i` is the segment between the ends** `fanTri V i 1` and `fanTri V i 2`. -/
theorem IsSiteSystem.facet_eq_segment (hV : IsSiteSystem V r) (i : FanIndex V) :
    facet V i.1.1 i.1.2 = segment ℝ (fanTri V i 1) (fanTri V i 2) := by
  obtain ⟨-, he⟩ := hV.facetEnds_spec i.2
  rw [← hV.convexHull_extremePoints_facet i.2.1 i.2.2.1, he, convexHull_pair, fanTri_one,
    fanTri_two]

/-- **The fan triangles are nondegenerate**: the ends `a, b` of a nondegenerate facet are distinct
points of the bisector of `p` and `q`, which does not contain `p`. -/
theorem IsSiteSystem.cross_fanTri_ne_zero (hV : IsSiteSystem V r) (i : FanIndex V) :
    cross (fanTri V i 1 - fanTri V i 0) (fanTri V i 2 - fanTri V i 0) ≠ 0 := by
  obtain ⟨hne, he⟩ := hV.facetEnds_spec i.2
  have hmem : ∀ v ∈ (facet V i.1.1 i.1.2).extremePoints ℝ, bisector i.1.1 i.1.2 v = 0 :=
    fun v hv => ((mem_facet_iff_bisector i.2.1 i.2.2.1).1 (extremePoints_subset hv)).2
  rw [he] at hmem
  rw [fanTri_zero, fanTri_one, fanTri_two]
  exact fun hc => hne (eq_of_bisector_of_cross i.2.2.2.1 (hmem _ (mem_insert _ _))
    (hmem _ (mem_insert_of_mem _ (mem_singleton _))) hc)

/-- **The fan triangles form a triangulation of the plane**: they are nondegenerate, locally
finite, cover the plane (every tile is the union of its fan triangles), and two distinct fan
triangles meet in the convex hull of their common vertices. -/
theorem IsSiteSystem.isTriangulation_fanTri (hV : IsSiteSystem V r) :
    IsTriangulation (fanTri V) where
  nondeg i := hV.cross_fanTri_ne_zero i
  locallyFinite := by
    intro x
    refine ⟨closedBall x 1, closedBall_mem_nhds x one_pos, ?_⟩
    refine ((hV.finite_fanPairs_meeting (isCompact_closedBall x 1)).preimage
      Subtype.val_injective.injOn).subset fun i hi => ?_
    have hi' : (fan V i.1.1 i.1.2 ∩ closedBall x 1).Nonempty := by
      rw [← hV.tri_fanTri i]
      exact hi
    exact show IsFanPair V i.1.1 i.1.2 ∧ (fan V i.1.1 i.1.2 ∩ closedBall x 1).Nonempty from
      ⟨i.2, hi'⟩
  cover := by
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨p, hp, hx⟩ := hV.exists_mem_tile x
    rw [hV.tile_eq_iUnion_fan hp] at hx
    obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.1 hx
    refine mem_iUnion.2 ⟨⟨(p, q), hq⟩, ?_⟩
    rw [hV.tri_fanTri]
    exact hxq
  inter i j hij := by
    rw [hV.tri_fanTri i, hV.tri_fanTri j, ← hV.fanVerts_eq i, ← hV.fanVerts_eq j]
    exact (hV.fan_inter_fan i.2 j.2 fun h => hij (Subtype.ext h)).subset

/-! ## Tiles, shared pieces and cells as unions of faces -/

/-- **A tile is the union of its fan triangles**, indexed by the fan triangulation. -/
theorem IsSiteSystem.tile_eq_iUnion_tri (hV : IsSiteSystem V r) {p : Plane} (hp : p ∈ V) :
    tile V p = ⋃ (i : FanIndex V) (_ : i.1.1 = p), tri (fanTri V) i := by
  rw [hV.tile_eq_iUnion_fan hp]
  apply Subset.antisymm
  · refine iUnion₂_subset fun q hq x hx => mem_iUnion₂.2 ⟨⟨(p, q), hq⟩, rfl, ?_⟩
    rw [hV.tri_fanTri]
    exact hx
  · refine iUnion₂_subset ?_
    rintro ⟨⟨p', q⟩, h⟩ hi x hx
    obtain rfl : p' = p := hi
    rw [hV.tri_fanTri] at hx
    exact mem_iUnion₂.2 ⟨q, h, hx⟩

/-- The facet of `i` together with the spokes from the site to its ends is the union of the edges
of the fan triangle of `i`. -/
theorem IsSiteSystem.facet_union_spokes_eq_fanEdges (hV : IsSiteSystem V r) (i : FanIndex V) :
    facet V i.1.1 i.1.2 ∪ ⋃ v ∈ (facet V i.1.1 i.1.2).extremePoints ℝ, segment ℝ i.1.1 v =
      fanEdges V i := by
  obtain ⟨-, he⟩ := hV.facetEnds_spec i.2
  rw [fanEdges, fanTri_zero, fanTri_one, fanTri_two, he, biUnion_insert, biUnion_singleton,
    hV.facet_eq_segment i, fanTri_one, fanTri_two, union_assoc]

/-- **The shared piece of a tile is the union of the edges of its fan triangles.** -/
theorem IsSiteSystem.shared_eq_iUnion_fanEdges (hV : IsSiteSystem V r) {p : Plane} (hp : p ∈ V) :
    shared V p = ⋃ (i : FanIndex V) (_ : i.1.1 = p), fanEdges V i := by
  rw [hV.shared_eq_iUnion_edges hp]
  apply Subset.antisymm
  · refine iUnion₂_subset fun q hq x hx => mem_iUnion₂.2 ⟨⟨(p, q), hq⟩, rfl, ?_⟩
    exact (hV.facet_union_spokes_eq_fanEdges ⟨(p, q), hq⟩).subset hx
  · refine iUnion₂_subset fun i hi x hx => ?_
    have key := (hV.facet_union_spokes_eq_fanEdges i).symm.subset hx
    rw [hi] at key
    have h2 : IsFanPair V p i.1.2 := hi ▸ i.2
    exact mem_iUnion₂.2 ⟨i.1.2, h2, key⟩

namespace PolygonalInput

/-- **A polygonal cell is a union of fan triangles and fan triangle edges**: for each site `p` whose
tile meets the old cell `K_j`, the fan triangles of `Q_p` if `j` owns the tile, their edges
otherwise. -/
theorem cell_eq_iUnion_fanTri {I : PolygonalInput} (hV : IsSiteSystem I.V I.r) (j : ℤ) :
    I.cell j = ⋃ p ∈ I.sitesOf j,
      if I.owner p = j then ⋃ (i : FanIndex I.V) (_ : i.1.1 = p), tri (fanTri I.V) i
      else ⋃ (i : FanIndex I.V) (_ : i.1.1 = p), fanEdges I.V i := by
  unfold cell
  refine iUnion₂_congr fun p hp => ?_
  unfold piece
  split_ifs
  · exact hV.tile_eq_iUnion_tri hp.1
  · exact hV.shared_eq_iUnion_fanEdges hp.1

end PolygonalInput

end MatedCRT.ZeroConePolygonal
