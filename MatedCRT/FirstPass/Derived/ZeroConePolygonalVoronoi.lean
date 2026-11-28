import LatticeProb.Bonanno.ReflectedGMS.GMS.LineConnectedPoint
import Mathlib

/-!
# Voronoi tiles of a locally finite set of sites

The polygonal cell configuration of the written answer `notes/fp-gaps/CODEX-MQ-sbl-32.md` (lines 19-21)
is built from the closed Euclidean Voronoi tiles `Q_p` of a locally finite set `V` of sites, which is dense
relative to a positive `1`-Lipschitz scale function `r`: every point `z` has a site within `r(z) / 100`.
This file proves the facts about the tiles used there.

* `tile V p`: the closed Voronoi tile `Q_p = {y | |y - p| ≤ |y - q| for all q ∈ V}`; it is closed and
  convex and contains `p`.
* `IsSiteSystem V r`: the standing assumptions on the sites and the scale function.
* `IsSiteSystem.dist_le`: `y ∈ Q_p` gives `99 |y - p| ≤ r(p)` (answer, line 21); hence every tile is
  compact, with diameter at most `2 r(p) / 99`.
* `IsSiteSystem.exists_mem_tile`: the tiles cover the plane.
* `IsSiteSystem.exists_ball_subset_tile`: each tile contains a ball about its site.
* `volume_tile_inter`, `mem_frontier_of_mem_tile_inter`, `notMem_tile_of_mem_interior`: two distinct
  tiles meet in a Lebesgue-null set contained in the frontier of each, so an interior point of a tile
  lies in no other tile.
* `IsSiteSystem.finite_tiles_meeting`: only finitely many tiles meet a closed ball.
* `IsSiteSystem.dist_le_of_mem_tile_of_le`: a tile meeting a point `y` with `r(y) ≤ δ` lies within
  `δ / 40` of `y` (answer, line 21: "If `Q_p` meets `K_j` at `z`, ... `diam Q_p < δ_j / 40`").
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open ReflectedGMS

/-! ## Half-planes and lines -/

/-- Comparison of distances to two points is a linear inequality. -/
theorem dist_le_dist_iff_inner (y p q : Plane) :
    dist y p ≤ dist y q ↔ 2 * ⟪y, q - p⟫ ≤ ‖q‖ ^ 2 - ‖p‖ ^ 2 := by
  rw [← sq_le_sq₀ dist_nonneg dist_nonneg, dist_eq_norm, dist_eq_norm, norm_sub_sq_real,
    norm_sub_sq_real, inner_sub_right]
  constructor <;> intro h <;> linarith

/-- A closed half-plane is convex. -/
theorem convex_inner_le (v : Plane) (c : ℝ) : Convex ℝ {y : Plane | ⟪y, v⟫ ≤ c} := by
  intro x hx y hy a b ha hb hab
  change ⟪x, v⟫ ≤ c at hx
  change ⟪y, v⟫ ≤ c at hy
  change ⟪a • x + b • y, v⟫ ≤ c
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have hc : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

/-- A line lies in the frontier of the half-plane it bounds. -/
theorem inner_eq_subset_frontier (v : Plane) (hv : v ≠ 0) (c : ℝ) :
    {y : Plane | ⟪y, v⟫ = c} ⊆ frontier {y : Plane | ⟪y, v⟫ ≤ c} := by
  intro y hy
  change ⟪y, v⟫ = c at hy
  refine ⟨subset_closure (show ⟪y, v⟫ ≤ c from hy.le), fun hint => ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior y hint
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ε / (2 * ‖v‖) := ⟨_, rfl⟩
  have htpos : 0 < t := by rw [ht]; exact div_pos hε (mul_pos two_pos hvpos)
  have hnorm : t * ‖v‖ = ε / 2 := by
    rw [ht, div_mul_eq_mul_div, mul_div_mul_right _ _ hvpos.ne']
  have hmem : y + t • v ∈ ball y ε := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg htpos.le, hnorm]
    linarith
  have h1 : y + t • v ∈ {y : Plane | ⟪y, v⟫ ≤ c} := interior_subset (hball hmem)
  change ⟪y + t • v, v⟫ ≤ c at h1
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at h1
  have : 0 < t * ‖v‖ ^ 2 := mul_pos htpos (pow_pos hvpos 2)
  linarith

/-- A line in the plane is Lebesgue-null. -/
theorem volume_inner_eq_zero (v : Plane) (hv : v ≠ 0) (c : ℝ) :
    volume {y : Plane | ⟪y, v⟫ = c} = 0 :=
  measure_mono_null (inner_eq_subset_frontier v hv c) ((convex_inner_le v c).addHaar_frontier volume)

/-! ## Voronoi tiles -/

/-- **The closed Voronoi tile** `Q_p = {y | |y - p| ≤ |y - q| for all q ∈ V}` of the site `p` among the
sites `V` (answer, line 21). -/
def tile (V : Set Plane) (p : Plane) : Set Plane := {y | ∀ q ∈ V, dist y p ≤ dist y q}

theorem self_mem_tile (V : Set Plane) (p : Plane) : p ∈ tile V p := fun q _ => by
  rw [dist_self]
  exact dist_nonneg

theorem isClosed_tile (V : Set Plane) (p : Plane) : IsClosed (tile V p) := by
  have h : tile V p = ⋂ q ∈ V, {y : Plane | dist y p ≤ dist y q} := by
    ext y
    exact ⟨fun h => Set.mem_iInter₂.2 h, fun h => Set.mem_iInter₂.1 h⟩
  rw [h]
  exact isClosed_biInter fun q _ => isClosed_le (continuous_id.dist continuous_const)
    (continuous_id.dist continuous_const)

theorem convex_tile (V : Set Plane) (p : Plane) : Convex ℝ (tile V p) := by
  intro x hx y hy a b ha hb hab q hq
  have hx' := (dist_le_dist_iff_inner x p q).1 (hx q hq)
  have hy' := (dist_le_dist_iff_inner y p q).1 (hy q hq)
  rw [dist_le_dist_iff_inner, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have hc : a * (‖q‖ ^ 2 - ‖p‖ ^ 2) + b * (‖q‖ ^ 2 - ‖p‖ ^ 2) = ‖q‖ ^ 2 - ‖p‖ ^ 2 := by
    rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx' ha, mul_le_mul_of_nonneg_left hy' hb]

/-- A point of two tiles is equidistant from their sites. -/
theorem inner_eq_of_mem_tile_inter (V : Set Plane) {p q y : Plane} (hp : p ∈ V) (hq : q ∈ V)
    (hyp : y ∈ tile V p) (hyq : y ∈ tile V q) :
    2 * ⟪y, q - p⟫ = ‖q‖ ^ 2 - ‖p‖ ^ 2 := by
  have h1 := (dist_le_dist_iff_inner y p q).1 (hyp q hq)
  have h2 := (dist_le_dist_iff_inner y q p).1 (hyq p hp)
  have h3 : ⟪y, p - q⟫ = -⟪y, q - p⟫ := by rw [← inner_neg_right, neg_sub]
  linarith

/-- **Distinct tiles overlap in a null set.** -/
theorem volume_tile_inter (V : Set Plane) {p q : Plane} (hp : p ∈ V) (hq : q ∈ V) (hpq : p ≠ q) :
    volume (tile V p ∩ tile V q) = 0 := by
  have hv : (2 : ℝ) • (q - p) ≠ 0 := smul_ne_zero two_ne_zero (sub_ne_zero.2 hpq.symm)
  refine measure_mono_null (fun y hy => ?_) (volume_inner_eq_zero _ hv (‖q‖ ^ 2 - ‖p‖ ^ 2))
  change ⟪y, (2 : ℝ) • (q - p)⟫ = _
  rw [real_inner_smul_right]
  exact inner_eq_of_mem_tile_inter V hp hq hy.1 hy.2

/-- **An interior point of a tile lies in no other tile.** -/
theorem notMem_tile_of_mem_interior (V : Set Plane) {p q y : Plane} (hp : p ∈ V) (hq : q ∈ V)
    (hpq : p ≠ q) (hy : y ∈ interior (tile V p)) : y ∉ tile V q := by
  intro hyq
  have heq := inner_eq_of_mem_tile_inter V hp hq (interior_subset hy) hyq
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior y hy
  have hvpos : 0 < ‖q - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hpq.symm)
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ε / (2 * ‖q - p‖) := ⟨_, rfl⟩
  have htpos : 0 < t := by rw [ht]; exact div_pos hε (mul_pos two_pos hvpos)
  have hnorm : t * ‖q - p‖ = ε / 2 := by
    rw [ht, div_mul_eq_mul_div, mul_div_mul_right _ _ hvpos.ne']
  have hmem : y + t • (q - p) ∈ ball y ε := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg htpos.le, hnorm]
    linarith
  have h1 := (dist_le_dist_iff_inner _ p q).1 (interior_subset (hball hmem) q hq)
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at h1
  have : 0 < t * ‖q - p‖ ^ 2 := mul_pos htpos (pow_pos hvpos 2)
  linarith

/-- A point common to two distinct tiles lies on the frontier of each. -/
theorem mem_frontier_of_mem_tile_inter (V : Set Plane) {p q y : Plane} (hp : p ∈ V) (hq : q ∈ V)
    (hpq : p ≠ q) (hyp : y ∈ tile V p) (hyq : y ∈ tile V q) : y ∈ frontier (tile V p) :=
  ⟨subset_closure hyp, fun hint => notMem_tile_of_mem_interior V hp hq hpq hint hyq⟩

/-! ## Sites dense relative to a scale function -/

/-- **The standing assumptions on the sites** (answer, line 19): the scale function `r` is positive and
`1`-Lipschitz, the sites are locally finite, and every point `z` has a site within `r(z) / 100`. -/
structure IsSiteSystem (V : Set Plane) (r : Plane → ℝ) : Prop where
  lip : ∀ y z, r y ≤ r z + dist y z
  pos : ∀ z, 0 < r z
  finite : ∀ z R, (V ∩ closedBall z R).Finite
  dense : ∀ z, ∃ p ∈ V, dist z p ≤ r z / 100

variable {V : Set Plane} {r : Plane → ℝ}

/-- `y ∈ Q_p` gives `99 |y - p| ≤ r(p)` (answer, line 21). -/
theorem IsSiteSystem.dist_le (hV : IsSiteSystem V r) {p y : Plane} (hy : y ∈ tile V p) :
    99 * dist y p ≤ r p := by
  obtain ⟨q, hqV, hq⟩ := hV.dense y
  have h1 := hy q hqV
  have h2 := hV.lip y p
  linarith

theorem IsSiteSystem.tile_subset (hV : IsSiteSystem V r) (p : Plane) :
    tile V p ⊆ closedBall p (r p / 99) := fun y hy => by
  rw [mem_closedBall]
  have := hV.dist_le hy
  linarith

theorem IsSiteSystem.isCompact_tile (hV : IsSiteSystem V r) (p : Plane) : IsCompact (tile V p) :=
  (isCompact_closedBall p _).of_isClosed_subset (isClosed_tile V p) (hV.tile_subset p)

theorem IsSiteSystem.diam_tile_le (hV : IsSiteSystem V r) (p : Plane) :
    diam (tile V p) ≤ 2 * (r p / 99) := by
  apply Metric.diam_le_of_forall_dist_le (by have := hV.pos p; positivity)
  intro y hy y' hy'
  have h1 := hV.dist_le hy
  have h2 := hV.dist_le hy'
  have h3 := dist_triangle_right y y' p
  linarith

/-- **The tiles cover the plane**: a nearest site exists. -/
theorem IsSiteSystem.exists_mem_tile (hV : IsSiteSystem V r) (y : Plane) :
    ∃ p ∈ V, y ∈ tile V p := by
  classical
  obtain ⟨p₀, hp₀V, hp₀⟩ := hV.dense y
  have hfin := hV.finite y (r y)
  have hy0 := hV.pos y
  have hne : hfin.toFinset.Nonempty := ⟨p₀, hfin.mem_toFinset.2 ⟨hp₀V, by
    rw [mem_closedBall, dist_comm]
    linarith⟩⟩
  obtain ⟨p, hp, hmin⟩ := hfin.toFinset.exists_min_image (fun q => dist y q) hne
  rw [Set.Finite.mem_toFinset] at hp
  refine ⟨p, hp.1, fun q hq => ?_⟩
  by_cases hqb : q ∈ closedBall y (r y)
  · exact hmin q (hfin.mem_toFinset.2 ⟨hq, hqb⟩)
  · rw [mem_closedBall, not_le, dist_comm] at hqb
    have h2 := hp.2
    rw [mem_closedBall, dist_comm] at h2
    linarith

/-- **Each tile contains a ball about its site.** -/
theorem IsSiteSystem.exists_ball_subset_tile (hV : IsSiteSystem V r) (p : Plane) :
    ∃ ε > 0, ball p ε ⊆ tile V p := by
  have hfin : ((V ∩ closedBall p 1) \ {p}).Finite := (hV.finite p 1).subset Set.sdiff_subset
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.1 hfin.isClosed.isOpen_compl p (fun h => h.2 rfl)
  refine ⟨min ε 1 / 2, by positivity, fun y hy q hq => ?_⟩
  rw [mem_ball] at hy
  by_cases hqp : q = p
  · subst hqp
    exact le_rfl
  · have hfar : min ε 1 ≤ dist q p := by
      by_cases hq1 : dist q p ≤ 1
      · by_contra hlt
        rw [not_le] at hlt
        exact hball (mem_ball.2 (lt_of_lt_of_le hlt (min_le_left _ _)))
          ⟨⟨hq, mem_closedBall.2 hq1⟩, hqp⟩
      · rw [not_le] at hq1
        exact (min_le_right _ _).trans hq1.le
    have h3 := dist_triangle q y p
    rw [dist_comm q y] at h3
    linarith

theorem IsSiteSystem.interior_tile_nonempty (hV : IsSiteSystem V r) (p : Plane) :
    (interior (tile V p)).Nonempty := by
  obtain ⟨ε, hε, hball⟩ := hV.exists_ball_subset_tile p
  exact ⟨p, interior_maximal hball isOpen_ball (mem_ball_self hε)⟩

/-- **Only finitely many tiles meet a closed ball.** -/
theorem IsSiteSystem.finite_tiles_meeting (hV : IsSiteSystem V r) (z : Plane) (R : ℝ) :
    {p ∈ V | (tile V p ∩ closedBall z R).Nonempty}.Finite := by
  apply (hV.finite z (R + (r z + R) / 98)).subset
  rintro p ⟨hpV, y, hyp, hyz⟩
  refine ⟨hpV, ?_⟩
  rw [mem_closedBall] at hyz ⊢
  have h1 := hV.dist_le hyp
  have h2 := hV.lip p y
  have h3 := hV.lip y z
  have h4 := dist_triangle p y z
  rw [dist_comm p y] at h2 h4
  linarith

/-- **A tile meeting a point of small scale is small** (answer, line 21): if `y ∈ Q_p` and `r(y) ≤ δ`,
every point of `Q_p` lies within `δ / 40` of `y`. -/
theorem IsSiteSystem.dist_le_of_mem_tile_of_le (hV : IsSiteSystem V r) {p y y' : Plane} {δ : ℝ}
    (hy : y ∈ tile V p) (hry : r y ≤ δ) (hy' : y' ∈ tile V p) : dist y' y ≤ δ / 40 := by
  have h1 := hV.dist_le hy
  have h2 := hV.dist_le hy'
  have h3 := hV.lip p y
  have h4 := dist_triangle y' p y
  have h5 := hV.pos y
  rw [dist_comm p y] at h3 h4
  linarith

end MatedCRT.ZeroConePolygonal
