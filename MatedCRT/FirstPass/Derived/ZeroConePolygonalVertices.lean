import MatedCRT.FirstPass.Derived.ZeroConePolygonalVoronoi

/-!
# Vertices and spokes of the Voronoi tiles

For a locally finite set `V` of sites dense relative to a scale function `r` (`IsSiteSystem V r`) the tile
`Q_p` is a bounded convex polygon (written answer `answers/51-zero-cone-annulus-premise.md`, line 21). Near
its site only the finitely many sites of `nearSites V p R` constrain it, so every vertex of the tile lies on
the bisectors of two of them with non-parallel normals.

* `tileVertices V p`: the extreme points of the tile `Q_p`.
* `IsSiteSystem.finite_tileVertices`: there are finitely many (answer, line 21: "Each tile is a bounded
  convex polygon").
* `IsSiteSystem.tileVertices_nonempty`, `tileVertices_subset_frontier`: there is at least one, and the
  vertices lie in the frontier of the tile.
* `shared V p`: the piece of the tile given to every label meeting it: its frontier together with the
  segments from the site `p` to all the vertices of the tile (answer, line 23: "Give its boundary and the
  segments from `p` to all its vertices to every one of those labels").
* `shared_subset_tile`, `self_mem_shared`, `isClosed_shared`, `volume_shared`, `tile_inter_subset_shared`,
  `IsSiteSystem.isConnected_shared`, `IsSiteSystem.isCompact_shared`,
  `IsSiteSystem.exists_mem_interior_notMem_shared`: the shared piece is a compact connected null subset of
  the tile containing the site, which contains the intersection of the tile with every other tile and
  misses some interior point of the tile.
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open ReflectedGMS

variable {V : Set Plane} {r : Plane → ℝ}

/-! ## Coordinates -/

theorem inner_eq_coord (x y : Plane) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- The quarter turn of a vector of the plane. -/
def perp (u : Plane) : Plane := !₂[-u 1, u 0]

@[simp] theorem perp_apply_zero (u : Plane) : perp u 0 = -u 1 := rfl

@[simp] theorem perp_apply_one (u : Plane) : perp u 1 = u 0 := rfl

theorem perp_ne_zero {u : Plane} (hu : u ≠ 0) : perp u ≠ 0 := fun h => hu (by
  have h0 : perp u 0 = 0 := by rw [h]; rfl
  have h1 : perp u 1 = 0 := by rw [h]; rfl
  simp only [perp_apply_zero, perp_apply_one] at h0 h1
  ext i
  fin_cases i
  · simpa using h1
  · simpa using (neg_eq_zero.1 h0))

theorem inner_perp (u w : Plane) : ⟪w, perp u⟫ = u 0 * w 1 - u 1 * w 0 := by
  rw [inner_eq_coord]
  simp
  ring

/-- The determinant of two vectors of the plane. -/
def cross (u w : Plane) : ℝ := u 0 * w 1 - u 1 * w 0

theorem eq_of_cross_ne_zero {u w a b : Plane} (h : cross u w ≠ 0) (hu : ⟪a - b, u⟫ = 0)
    (hw : ⟪a - b, w⟫ = 0) : a = b := by
  rw [inner_eq_coord] at hu hw
  simp only [PiLp.sub_apply] at hu hw
  unfold cross at h
  have h0 : (a 0 - b 0) * (u 0 * w 1 - u 1 * w 0) = 0 := by linear_combination w 1 * hu - u 1 * hw
  have h1 : (a 1 - b 1) * (u 0 * w 1 - u 1 * w 0) = 0 := by linear_combination u 0 * hw - w 0 * hu
  have e0 := (mul_eq_zero.1 h0).resolve_right h
  have e1 := (mul_eq_zero.1 h1).resolve_right h
  ext i
  fin_cases i
  · exact sub_eq_zero.1 e0
  · exact sub_eq_zero.1 e1

/-! ## The bisector form of two sites -/

/-- The affine form `‖q‖² - ‖p‖² - 2 ⟪y, q - p⟫ = |y - q|² - |y - p|²`, nonnegative exactly on the side
of the bisector of `p` and `q` containing `p`. -/
def bisector (p q y : Plane) : ℝ := ‖q‖ ^ 2 - ‖p‖ ^ 2 - 2 * ⟪y, q - p⟫

theorem dist_le_dist_iff_bisector (p q y : Plane) : dist y p ≤ dist y q ↔ 0 ≤ bisector p q y := by
  rw [dist_le_dist_iff_inner]
  unfold bisector
  constructor <;> intro h <;> linarith

theorem bisector_add_smul (p q v d : Plane) (t : ℝ) :
    bisector p q (v + t • d) = bisector p q v - 2 * t * ⟪d, q - p⟫ := by
  unfold bisector
  rw [inner_add_left, real_inner_smul_left]
  ring

/-! ## The vertices of a tile -/

/-- The sites near `p` which can bound the tile near `p`: those within `2 R` of `p`. -/
def nearSites (V : Set Plane) (p : Plane) (R : ℝ) : Set Plane := V ∩ closedBall p (2 * R)

/-- A point within `R` of `p` lies in the tile as soon as it satisfies the constraints of the near sites. -/
theorem mem_tile_of_nearSites {p w : Plane} {R : ℝ} (hw : dist w p ≤ R)
    (h : ∀ q ∈ nearSites V p R, dist w p ≤ dist w q) : w ∈ tile V p := by
  intro q hq
  by_cases hqp : dist q p ≤ 2 * R
  · exact h q ⟨hq, mem_closedBall.2 hqp⟩
  · rw [not_le] at hqp
    have := dist_triangle q w p
    rw [dist_comm q w] at this
    linarith

/-- **The vertices of the tile** `Q_p`: its extreme points. -/
def tileVertices (V : Set Plane) (p : Plane) : Set Plane := (tile V p).extremePoints ℝ

theorem tileVertices_subset_tile (V : Set Plane) (p : Plane) : tileVertices V p ⊆ tile V p :=
  extremePoints_subset

/-- A vertex of the tile lies on the bisectors of two near sites with non-parallel normals. -/
theorem IsSiteSystem.exists_pair_of_mem_tileVertices (hV : IsSiteSystem V r) {p v : Plane}
    (hv : v ∈ tileVertices V p) :
    ∃ q₁ ∈ nearSites V p (r p / 99 + 1), ∃ q₂ ∈ nearSites V p (r p / 99 + 1),
      cross (q₁ - p) (q₂ - p) ≠ 0 ∧ bisector p q₁ v = 0 ∧ bisector p q₂ v = 0 := by
  set R := r p / 99 + 1 with hR
  by_contra hcon
  push Not at hcon
  have hvt : v ∈ tile V p := tileVertices_subset_tile V p hv
  have hrp := hV.pos p
  have hvR : dist v p < R := by
    have := hV.dist_le hvt
    rw [hR]
    linarith
  have hfin : (nearSites V p R).Finite := (hV.finite p (2 * R)).subset fun q hq => hq
  have hnn : ∀ q ∈ nearSites V p R, 0 ≤ bisector p q v := fun q hq =>
    (dist_le_dist_iff_bisector p q v).1 (hvt q hq.1)
  obtain ⟨d, hd0, hd⟩ : ∃ d : Plane, d ≠ 0 ∧ ∀ q ∈ nearSites V p R,
      q ≠ p → bisector p q v = 0 → ⟪d, q - p⟫ = 0 := by
    by_cases hS : ∃ q₀ ∈ nearSites V p R, q₀ ≠ p ∧ bisector p q₀ v = 0
    · obtain ⟨q₀, hq₀, hq₀p, hq₀b⟩ := hS
      refine ⟨perp (q₀ - p), perp_ne_zero (sub_ne_zero.2 hq₀p), fun q hq _ hqb => ?_⟩
      have h1 := hcon q₀ hq₀ q hq
      have h2 : cross (q₀ - p) (q - p) = 0 := by
        by_contra hne
        exact h1 hne hq₀b hqb
      rw [real_inner_comm, inner_perp]
      exact h2
    · push Not at hS
      exact ⟨EuclideanSpace.single 0 1, fun h => by
        have := congrArg (fun x : Plane => x 0) h
        simp at this, fun q hq hqp hqb => absurd hqb (hS q hq hqp)⟩
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), dist (v + t • d) p < R ∧
      ∀ q ∈ nearSites V p R, 0 ≤ bisector p q (v + t • d) := by
    refine Filter.Eventually.and ?_ ((Filter.eventually_all_finite hfin).2 fun q hq => ?_)
    · have hc : Continuous fun t : ℝ => dist (v + t • d) p := by fun_prop
      exact hc.continuousAt.eventually_lt continuousAt_const (by simpa using hvR)
    · by_cases hq0 : bisector p q v = 0
      · refine Filter.Eventually.of_forall fun t => ?_
        by_cases hqp : q = p
        · subst hqp
          simp [bisector]
        · rw [bisector_add_smul, hq0, hd q hq hqp hq0]
          simp
      · have hpos : 0 < bisector p q v := lt_of_le_of_ne (hnn q hq) (Ne.symm hq0)
        have hc : Continuous fun t : ℝ => bisector p q (v + t • d) := by
          simp only [bisector_add_smul]
          fun_prop
        exact (hc.tendsto 0).eventually (lt_mem_nhds (by simpa using hpos)) |>.mono fun t ht => ht.le
  obtain ⟨δ, hδ, hδt⟩ := Metric.eventually_nhds_iff.1 hev
  set t : ℝ := δ / 2 with ht
  have htpos : 0 < t := by positivity
  have hmem : ∀ s : ℝ, dist s 0 < δ → v + s • d ∈ tile V p := fun s hs => by
    obtain ⟨h1, h2⟩ := hδt hs
    exact mem_tile_of_nearSites h1.le fun q hq => (dist_le_dist_iff_bisector p q _).2 (h2 q hq)
  have hdt : dist t 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos htpos]
    linarith
  have hdt' : dist (-t) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos htpos]
    linarith
  have hseg : v ∈ openSegment ℝ (v + t • d) (v + (-t) • d) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by module⟩
  have := (hv.2 (hmem t hdt) (hmem (-t) hdt') hseg)
  have h0 : t • d = 0 := by simpa using this
  exact hd0 ((smul_eq_zero.1 h0).resolve_left htpos.ne')

/-- **A tile has finitely many vertices** (answer, line 21: "Each tile is a bounded convex polygon"). -/
theorem IsSiteSystem.finite_tileVertices (hV : IsSiteSystem V r) (p : Plane) :
    (tileVertices V p).Finite := by
  have hfin : (nearSites V p (r p / 99 + 1)).Finite := (hV.finite p _).subset fun q hq => hq
  refine (hfin.biUnion fun q₁ _ => hfin.biUnion fun q₂ _ =>
    (show ({y | cross (q₁ - p) (q₂ - p) ≠ 0 ∧ bisector p q₁ y = 0 ∧ bisector p q₂ y = 0} :
      Set Plane).Finite from ?_)).subset ?_
  · refine Set.Subsingleton.finite fun a ha b hb => ?_
    refine eq_of_cross_ne_zero ha.1 ?_ ?_
    · have h1 := ha.2.1
      have h2 := hb.2.1
      unfold bisector at h1 h2
      rw [inner_sub_left]
      linarith
    · have h1 := ha.2.2
      have h2 := hb.2.2
      unfold bisector at h1 h2
      rw [inner_sub_left]
      linarith
  · intro v hv
    obtain ⟨q₁, h₁, q₂, h₂, hc, hb₁, hb₂⟩ := hV.exists_pair_of_mem_tileVertices hv
    exact mem_iUnion₂.2 ⟨q₁, h₁, mem_iUnion₂.2 ⟨q₂, h₂, hc, hb₁, hb₂⟩⟩

theorem IsSiteSystem.tileVertices_nonempty (hV : IsSiteSystem V r) (p : Plane) :
    (tileVertices V p).Nonempty :=
  (hV.isCompact_tile p).extremePoints_nonempty ⟨p, self_mem_tile V p⟩

/-- The vertices of a tile lie in its frontier. -/
theorem tileVertices_subset_frontier (V : Set Plane) (p : Plane) :
    tileVertices V p ⊆ frontier (tile V p) := fun _ hv =>
  ⟨subset_closure (tileVertices_subset_tile V p hv),
    fun h => Set.disjoint_left.1 (disjoint_interior_extremePoints (tile V p)) h hv⟩

/-! ## The shared pieces of the tiles -/

/-- **The shared piece** `S_p` of the tile `Q_p`: its frontier together with the segments from the site `p`
to all the vertices of the tile. It is given to every label whose old cell meets the tile (answer, line 23:
"Give its boundary and the segments from `p` to all its vertices to every one of those labels"). -/
def shared (V : Set Plane) (p : Plane) : Set Plane :=
  frontier (tile V p) ∪ ⋃ v ∈ tileVertices V p, segment ℝ p v

theorem shared_subset_tile (V : Set Plane) (p : Plane) : shared V p ⊆ tile V p := by
  rintro y (hy | hy)
  · exact (isClosed_tile V p).frontier_subset hy
  · obtain ⟨v, hv, hyv⟩ := mem_iUnion₂.1 hy
    exact (convex_tile V p).segment_subset (self_mem_tile V p) (tileVertices_subset_tile V p hv) hyv

theorem self_mem_shared (hV : IsSiteSystem V r) (p : Plane) : p ∈ shared V p := by
  obtain ⟨v, hv⟩ := hV.tileVertices_nonempty p
  exact Or.inr (mem_iUnion₂.2 ⟨v, hv, left_mem_segment ℝ p v⟩)

theorem isCompact_segment_plane (p v : Plane) : IsCompact (segment ℝ p v) := by
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

theorem isClosed_shared (hV : IsSiteSystem V r) (p : Plane) : IsClosed (shared V p) :=
  isClosed_frontier.union
    ((hV.finite_tileVertices p).isClosed_biUnion fun _ _ => (isCompact_segment_plane _ _).isClosed)

theorem volume_segment_eq_zero (p v : Plane) : volume (segment ℝ p v) = 0 := by
  by_cases hpv : v = p
  · subst hpv
    rw [segment_same]
    exact measure_singleton _
  · refine measure_mono_null (t := {y : Plane | ⟪y, perp (v - p)⟫ = ⟪p, perp (v - p)⟫}) ?_
      (volume_inner_eq_zero _ (perp_ne_zero (sub_ne_zero.2 hpv)) _)
    rintro _ ⟨a, b, ha, hb, hab, rfl⟩
    have h : ⟪v, perp (v - p)⟫ = ⟪p, perp (v - p)⟫ := by
      have := inner_perp (v - p) (v - p)
      rw [inner_sub_left] at this
      linarith [show (v - p) 0 * (v - p) 1 - (v - p) 1 * (v - p) 0 = 0 by ring]
    change ⟪a • p + b • v, perp (v - p)⟫ = _
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, h, ← add_mul, hab, one_mul]

/-- **The shared piece is Lebesgue-null.** -/
theorem volume_shared (hV : IsSiteSystem V r) (p : Plane) : volume (shared V p) = 0 :=
  measure_union_null ((convex_tile V p).addHaar_frontier volume)
    ((measure_biUnion_null_iff (hV.finite_tileVertices p).countable).2 fun v _ =>
      volume_segment_eq_zero p v)

/-- Two distinct tiles meet inside the shared piece of each. -/
theorem tile_inter_subset_shared {V : Set Plane} {p q : Plane} (hp : p ∈ V) (hq : q ∈ V)
    (hpq : p ≠ q) : tile V p ∩ tile V q ⊆ shared V p :=
  fun _ hy => Or.inl (mem_frontier_of_mem_tile_inter V hp hq hpq hy.1 hy.2)

/-- The plane has real dimension `2 > 1`. -/
theorem one_lt_rank_plane : 1 < Module.rank ℝ Plane := by
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  exact_mod_cast (one_lt_two : (1 : ℕ) < 2)

/-- **The frontier of a bounded convex set with interior in the plane is connected**: it is
homeomorphic to the unit circle. -/
theorem isConnected_frontier_of_convex {s : Set Plane} (hc : Convex ℝ s) (hne : (interior s).Nonempty)
    (hb : Bornology.IsBounded s) : IsConnected (frontier s) := by
  obtain ⟨h, -, -, hfr⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hne hb
  have hs : IsConnected (sphere (0 : Plane) 1) := isConnected_sphere one_lt_rank_plane 0 zero_le_one
  have h2 := hs.image h.symm h.symm.continuous.continuousOn
  rw [← hfr, Set.image_image] at h2
  simpa using h2

theorem IsSiteSystem.isConnected_frontier_tile (hV : IsSiteSystem V r) (p : Plane) :
    IsConnected (frontier (tile V p)) :=
  isConnected_frontier_of_convex (convex_tile V p) (hV.interior_tile_nonempty p)
    (isBounded_closedBall.subset (hV.tile_subset p))

/-- **The shared piece of a tile is connected**: its frontier is connected and every spoke joins the site
to a vertex on the frontier. -/
theorem IsSiteSystem.isConnected_shared (hV : IsSiteSystem V r) (p : Plane) :
    IsConnected (shared V p) := by
  obtain ⟨v₀, hv₀⟩ := hV.tileVertices_nonempty p
  have hU : IsPreconnected (⋃ v ∈ tileVertices V p, segment ℝ p v) := by
    have := isPreconnected_sUnion p ((fun v => segment ℝ p v) '' tileVertices V p)
      (by rintro _ ⟨v, -, rfl⟩; exact left_mem_segment ℝ p v)
      (by rintro _ ⟨v, -, rfl⟩; exact (convex_segment p v).isPreconnected)
    rwa [sUnion_image] at this
  exact (hV.isConnected_frontier_tile p).union
    ⟨v₀, tileVertices_subset_frontier V p hv₀, mem_iUnion₂.2 ⟨v₀, hv₀, right_mem_segment ℝ p v₀⟩⟩
    ⟨⟨p, mem_iUnion₂.2 ⟨v₀, hv₀, left_mem_segment ℝ p v₀⟩⟩, hU⟩

theorem IsSiteSystem.isCompact_shared (hV : IsSiteSystem V r) (p : Plane) : IsCompact (shared V p) :=
  (hV.isCompact_tile p).of_isClosed_subset (isClosed_shared hV p) (shared_subset_tile V p)

/-- **An interior point of a tile off its shared piece.** -/
theorem IsSiteSystem.exists_mem_interior_notMem_shared (hV : IsSiteSystem V r) (p : Plane) :
    ∃ y ∈ interior (tile V p), y ∉ shared V p := by
  by_contra hne
  have hsub : interior (tile V p) ⊆ shared V p := fun y hy => by
    by_contra hys
    exact hne ⟨y, hy, hys⟩
  have hpos := isOpen_interior.measure_pos volume (hV.interior_tile_nonempty p)
  rw [measure_mono_null hsub (volume_shared hV p)] at hpos
  exact lt_irrefl _ hpos

end MatedCRT.ZeroConePolygonal
