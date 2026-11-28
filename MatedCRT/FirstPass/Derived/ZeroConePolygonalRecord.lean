import MatedCRT.FirstPass.Derived.ZeroConePolygonalData
import MatedCRT.FirstPass.Derived.ZeroConePolygonalMatch

/-!
# The finite records of the polygonal patches

The Borel measurability of the polygonal cell configuration, in the topology on cell configurations
of Gwynne–Miller–Sheffield (arXiv:1807.07515v3, (1.14)–(1.15), p. 15), approximates the
configuration of a unit-mesh datum `w` by configurations chosen from countably many classes of
finite records. For each integer `R ≥ 1` the record keeps every cell meeting the closed ball of
radius `R` about the origin in its entirety: its label, the pieces of which it is the union and the
conductances between the recorded labels (including zeros). At stage `n` it also keeps the dyadic
bin of side `2^{-n}` of each recorded point.

The pieces are described through the fan triangles of the Voronoi tiles
(`ZeroConePolygonalFan`): an owned tile is the union of its fan triangles, and the shared piece of
any other tile is the union of the facets and spokes of its fan triangles. The points are named by
rational data: a site `η(t)` by its dyadic time `t`, and a vertex of the tile of `η(t)` by `t` and
the times `t₁, t₂` of two further sites, as the point equidistant from the three sites.

* `VName`, `namedPoint w`: names of points and their positions (`triCircumcenter` for vertices).
* `siteTimes w`: the dyadic times of the sites; `mem_sites_iff`, `UnitMeshValid.finite_siteTimes`.
* `PatchRecord`: the countable type of records; `patchRecord n R w`, `record n w` (`none` exactly
  off the valid data, `record_eq_none_iff`).
* `PatchRecord.canon`, `PatchRecord.faces`, `PatchRecord.nameSet`: canonical names (one recorded
  name per point, read off the record) and the faces of the cells in canonical names.
* `patchLabels w R`, `patchNames w R`, `patchFaces w R`: the labels, canonical names and faces of
  the patch of radius `R`, which do not depend on the stage `n`.
* `cell_eq_iUnion_patchFaces`: for every label `j` of the patch, the cell of `j` is the union of
  the convex hulls of the named points of the faces of `j`; `face_spec`: each face names vertices
  of a single fan triangle; `injOn_namedPoint_patchNames`: distinct canonical names name distinct
  points.
* `dist_namedPoint_le_of_patchRecord_eq`, `cond_eq_of_patchRecord_eq`: data with equal patch records
  at stage `n` place each canonical name within `2 · 2^{-n}` and have the same conductances.
* `patchMatch_of_record_eq`: two valid data with the same record at stage `n` have matched patches
  (`PatchMatch`) of every radius `1 ≤ R ≤ n`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open ReflectedGMS

/-! ## Finite sets of a set -/

/-- The finite set of the elements of `s` when `s` is finite, and `∅` otherwise. -/
def finsetOf {α : Type*} (s : Set α) : Finset α :=
  open Classical in if h : s.Finite then h.toFinset else ∅

theorem mem_of_mem_finsetOf {α : Type*} {s : Set α} {a : α} (ha : a ∈ finsetOf s) : a ∈ s := by
  unfold finsetOf at ha
  split_ifs at ha with h
  · exact h.mem_toFinset.1 ha
  · simp at ha

theorem mem_finsetOf {α : Type*} {s : Set α} (hs : s.Finite) {a : α} : a ∈ finsetOf s ↔ a ∈ s := by
  unfold finsetOf
  rw [dite_eq_left hs]
  exact hs.mem_toFinset

theorem coe_finsetOf {α : Type*} {s : Set α} (hs : s.Finite) : (finsetOf s : Set α) = s := by
  ext a
  rw [Finset.mem_coe, mem_finsetOf hs]

/-! ## The point equidistant from three sites -/

/-- The point equidistant from `p, q₁, q₂` when `cross (q₁ - p) (q₂ - p) ≠ 0`: the solution of
`⟪y, qᵢ - p⟫ = (‖qᵢ‖² - ‖p‖²) / 2` (`i = 1, 2`) by Cramer's rule. -/
def triCircumcenter (p q₁ q₂ : Plane) : Plane :=
  !₂[((‖q₁‖ ^ 2 - ‖p‖ ^ 2) / 2 * (q₂ - p) 1 - (‖q₂‖ ^ 2 - ‖p‖ ^ 2) / 2 * (q₁ - p) 1) /
      cross (q₁ - p) (q₂ - p),
    ((q₁ - p) 0 * ((‖q₂‖ ^ 2 - ‖p‖ ^ 2) / 2) - (q₂ - p) 0 * ((‖q₁‖ ^ 2 - ‖p‖ ^ 2) / 2)) /
      cross (q₁ - p) (q₂ - p)]

theorem triCircumcenter_apply_zero (p q₁ q₂ : Plane) :
    triCircumcenter p q₁ q₂ 0 =
      ((‖q₁‖ ^ 2 - ‖p‖ ^ 2) / 2 * (q₂ - p) 1 - (‖q₂‖ ^ 2 - ‖p‖ ^ 2) / 2 * (q₁ - p) 1) /
        cross (q₁ - p) (q₂ - p) :=
  rfl

theorem triCircumcenter_apply_one (p q₁ q₂ : Plane) :
    triCircumcenter p q₁ q₂ 1 =
      ((q₁ - p) 0 * ((‖q₂‖ ^ 2 - ‖p‖ ^ 2) / 2) - (q₂ - p) 0 * ((‖q₁‖ ^ 2 - ‖p‖ ^ 2) / 2)) /
        cross (q₁ - p) (q₂ - p) :=
  rfl

theorem inner_triCircumcenter_left {p q₁ q₂ : Plane} (h : cross (q₁ - p) (q₂ - p) ≠ 0) :
    ⟪triCircumcenter p q₁ q₂, q₁ - p⟫ = (‖q₁‖ ^ 2 - ‖p‖ ^ 2) / 2 := by
  rw [inner_eq_coord, triCircumcenter_apply_zero, triCircumcenter_apply_one]
  generalize (‖q₁‖ ^ 2 - ‖p‖ ^ 2) / 2 = c₁
  generalize (‖q₂‖ ^ 2 - ‖p‖ ^ 2) / 2 = c₂
  generalize q₁ - p = u at h ⊢
  generalize q₂ - p = v at h ⊢
  unfold cross at h ⊢
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff h]
  ring

theorem inner_triCircumcenter_right {p q₁ q₂ : Plane} (h : cross (q₁ - p) (q₂ - p) ≠ 0) :
    ⟪triCircumcenter p q₁ q₂, q₂ - p⟫ = (‖q₂‖ ^ 2 - ‖p‖ ^ 2) / 2 := by
  rw [inner_eq_coord, triCircumcenter_apply_zero, triCircumcenter_apply_one]
  generalize (‖q₁‖ ^ 2 - ‖p‖ ^ 2) / 2 = c₁
  generalize (‖q₂‖ ^ 2 - ‖p‖ ^ 2) / 2 = c₂
  generalize q₁ - p = u at h ⊢
  generalize q₂ - p = v at h ⊢
  unfold cross at h ⊢
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff h]
  ring

/-- A point on the bisectors of `p, q₁` and of `p, q₂`, with `q₁ - p` and `q₂ - p` not parallel, is
the point equidistant from the three sites. -/
theorem eq_triCircumcenter {p q₁ q₂ v : Plane} (h : cross (q₁ - p) (q₂ - p) ≠ 0)
    (h₁ : bisector p q₁ v = 0) (h₂ : bisector p q₂ v = 0) : v = triCircumcenter p q₁ q₂ := by
  have e₁ := inner_triCircumcenter_left h
  have e₂ := inner_triCircumcenter_right h
  unfold bisector at h₁ h₂
  refine eq_of_cross_ne_zero h ?_ ?_
  · rw [inner_sub_left]
    linarith
  · rw [inner_sub_left]
    linarith

/-! ## Names of points -/

/-- **Names of points**: a site `η(t)` is named by its time `t`, a vertex of the tile of `η(t)` by
`(t, t₁, t₂)`, the times of the site and of two further sites. -/
abbrev VName : Type := ℚ ⊕ (ℚ × ℚ × ℚ)

/-- **The point named by a name** in the datum `w`. -/
def namedPoint (w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) : VName → Plane
  | .inl t => curvePlane w t
  | .inr a => triCircumcenter (curvePlane w a.1) (curvePlane w a.2.1) (curvePlane w a.2.2)

@[simp]
theorem namedPoint_inl (w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) (t : ℚ) :
    namedPoint w (.inl t) = curvePlane w t :=
  rfl

@[simp]
theorem namedPoint_inr (w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) (a : ℚ × ℚ × ℚ) :
    namedPoint w (.inr a) =
      triCircumcenter (curvePlane w a.1) (curvePlane w a.2.1) (curvePlane w a.2.2) :=
  rfl

/-! ## The dyadic times of the sites -/

/-- The dyadic time `j - 1 + k 2^{-n}` as a rational number. -/
def dyadicTime (j : ℤ) (n k : ℕ) : ℚ := j - 1 + k * (1 / 2) ^ n

theorem cast_dyadicTime (j : ℤ) (n k : ℕ) : ((dyadicTime j n k : ℚ) : ℝ) = dyadicPoint j n k := by
  simp [dyadicTime, dyadicPoint]

variable {w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)}

variable (w) in
/-- **The dyadic times of the sites** of the datum `w`. -/
def siteTimes : Set ℚ :=
  {t | ∃ j : ℤ, ∃ k ≤ 2 ^ dyadicLevel (curvePlane w) (scaleFun (unitCell w) w.2) j,
    t = dyadicTime j (dyadicLevel (curvePlane w) (scaleFun (unitCell w) w.2) j) k}

/-- The sites are the points of the curve at the dyadic times of the sites. -/
theorem mem_sites_iff {p : Plane} :
    p ∈ (polygonalInputOf w).V ↔ ∃ t ∈ siteTimes w, curvePlane w t = p := by
  constructor
  · intro hp
    have hp' : p ∈ ⋃ j, cellSites (curvePlane w) (scaleFun (unitCell w) w.2) j := hp
    obtain ⟨j, k, hk, rfl⟩ := mem_iUnion.1 hp'
    exact ⟨_, ⟨j, k, hk, rfl⟩, by rw [cast_dyadicTime]⟩
  · rintro ⟨t, ⟨j, k, hk, rfl⟩, rfl⟩
    show _ ∈ ⋃ j, cellSites (curvePlane w) (scaleFun (unitCell w) w.2) j
    exact mem_iUnion.2 ⟨j, k, hk, by rw [cast_dyadicTime]⟩

/-- Only finitely many dyadic times of sites have their site in a compact set. -/
theorem UnitMeshValid.finite_siteTimes (h : UnitMeshValid w) {A : Set Plane} (hA : IsCompact A) :
    {t | t ∈ siteTimes w ∧ curvePlane w t ∈ A}.Finite := by
  refine ((h.lf A hA).biUnion fun j _ =>
    (Set.finite_Iic (2 ^ dyadicLevel (curvePlane w) (scaleFun (unitCell w) w.2) j)).image
      (dyadicTime j (dyadicLevel (curvePlane w) (scaleFun (unitCell w) w.2) j))).subset ?_
  rintro t ⟨⟨j, k, hk, rfl⟩, htA⟩
  refine mem_iUnion₂.2 ⟨j, ⟨_, ?_, htA⟩, k, hk, rfl⟩
  rw [← timeCell_curvePlane, cast_dyadicTime]
  exact mem_image_of_mem _ (dyadicPoint_mem_Icc j _ hk)

/-! ## The recorded objects -/

variable (w) in
/-- The labels of the cells meeting the closed ball of radius `R` about the origin. -/
def labelSet (R : ℕ) : Set ℤ := {j | ((polygonalInputOf w).cell j ∩ closedBall 0 R).Nonempty}

variable (w) in
/-- The dyadic times of the sites whose tile meets the old cell of a label of `labelSet w R`. -/
def tileTimes (R : ℕ) : Set ℚ :=
  {t | t ∈ siteTimes w ∧ ∃ j ∈ labelSet w R, j ∈ (polygonalInputOf w).labels (curvePlane w t)}

variable (w) in
/-- The pairs of times `(t, t')` with `t ∈ tileTimes w R` whose sites have a nondegenerate facet. -/
def fanTimes (R : ℕ) : Set (ℚ × ℚ) :=
  {tt | tt.1 ∈ tileTimes w R ∧ tt.2 ∈ siteTimes w ∧
    IsFanPair (polygonalInputOf w).V (curvePlane w tt.1) (curvePlane w tt.2)}

variable (w) in
/-- The names `(t, t₁, t₂)` of the extreme points of the facet of the sites `η(t), η(t')`, with
`η(t₁), η(t₂)` sites near `η(t)`. -/
def endNames (t t' : ℚ) : Set VName :=
  {a | ∃ t₁ ∈ siteTimes w, ∃ t₂ ∈ siteTimes w, a = .inr (t, t₁, t₂) ∧
    curvePlane w t₁ ∈ closedBall (curvePlane w t)
      (2 * ((polygonalInputOf w).r (curvePlane w t) / 99 + 1)) ∧
    curvePlane w t₂ ∈ closedBall (curvePlane w t)
      (2 * ((polygonalInputOf w).r (curvePlane w t) / 99 + 1)) ∧
    namedPoint w a ∈ (facet (polygonalInputOf w).V (curvePlane w t) (curvePlane w t')).extremePoints ℝ}

theorem UnitMeshValid.finite_tileTimes (h : UnitMeshValid w) (R : ℕ) : (tileTimes w R).Finite := by
  have hI := isValid_polygonalInputOf h
  have hL : (labelSet w R).Finite := hI.finite_cells_meeting 0 R
  have hP : (⋃ j ∈ labelSet w R, (polygonalInputOf w).sitesOf j).Finite :=
    hL.biUnion fun j _ => hI.finite_sitesOf j
  refine (h.finite_siteTimes hP.isCompact).subset ?_
  rintro t ⟨ht, j, hj, hjt⟩
  exact ⟨ht, mem_iUnion₂.2 ⟨j, hj, mem_sites_iff.2 ⟨t, ht, rfl⟩, hjt⟩⟩

theorem UnitMeshValid.finite_fanTimes (h : UnitMeshValid w) (R : ℕ) : (fanTimes w R).Finite := by
  have hT := h.finite_tileTimes R
  have hA : IsCompact (⋃ t ∈ tileTimes w R, closedBall (curvePlane w t)
      (2 * ((polygonalInputOf w).r (curvePlane w t) / 99 + 1))) :=
    hT.isCompact_biUnion fun t _ => isCompact_closedBall _ _
  refine (hT.prod (h.finite_siteTimes hA)).subset ?_
  rintro ⟨t, t'⟩ ⟨ht, ht', hfan⟩
  refine ⟨ht, ht', mem_iUnion₂.2 ⟨t, ht, ?_⟩⟩
  obtain ⟨y, hy⟩ := hfan.2.2.2.nonempty
  exact (h.isSiteSystem.mem_nearSites_of_mem_facet hfan.1 hfan.2.1 hy).2

theorem UnitMeshValid.finite_endNames (h : UnitMeshValid w) (t t' : ℚ) :
    (endNames w t t').Finite := by
  have hS := h.finite_siteTimes (isCompact_closedBall (curvePlane w t)
    (2 * ((polygonalInputOf w).r (curvePlane w t) / 99 + 1)))
  refine ((hS.prod hS).image fun tt : ℚ × ℚ => (.inr (t, tt.1, tt.2) : VName)).subset ?_
  rintro a ⟨t₁, ht₁, t₂, ht₂, rfl, h₁, h₂, -⟩
  exact ⟨(t₁, t₂), ⟨⟨ht₁, h₁⟩, ⟨ht₂, h₂⟩⟩, rfl⟩

/-- **The names of the facet ends name exactly the extreme points of the facet.** -/
theorem image_endNames (h : UnitMeshValid w) {t t' : ℚ} (ht : t ∈ siteTimes w)
    (ht' : t' ∈ siteTimes w) :
    namedPoint w '' endNames w t t' =
      (facet (polygonalInputOf w).V (curvePlane w t) (curvePlane w t')).extremePoints ℝ := by
  refine Subset.antisymm ?_ fun v hv => ?_
  · rintro _ ⟨a, ⟨t₁, -, t₂, -, -, -, -, ha⟩, rfl⟩
    exact ha
  have hpV : curvePlane w t ∈ (polygonalInputOf w).V := mem_sites_iff.2 ⟨t, ht, rfl⟩
  have hqV : curvePlane w t' ∈ (polygonalInputOf w).V := mem_sites_iff.2 ⟨t', ht', rfl⟩
  have hvt : v ∈ tileVertices (polygonalInputOf w).V (curvePlane w t) := by
    rw [extremePoints_facet hpV hqV] at hv
    exact hv.2
  obtain ⟨q₁, hq₁, q₂, hq₂, hcr, hb₁, hb₂⟩ := h.isSiteSystem.exists_pair_of_mem_tileVertices hvt
  obtain ⟨t₁, ht₁, rfl⟩ := mem_sites_iff.1 hq₁.1
  obtain ⟨t₂, ht₂, rfl⟩ := mem_sites_iff.1 hq₂.1
  have hname : namedPoint w (.inr (t, t₁, t₂)) = v := (eq_triCircumcenter hcr hb₁ hb₂).symm
  exact ⟨.inr (t, t₁, t₂), ⟨t₁, ht₁, t₂, ht₂, rfl, hq₁.2, hq₂.2, by rw [hname]; exact hv⟩, hname⟩

theorem namedPoint_mem_of_mem_endNames {t t' : ℚ} {a : VName} (ha : a ∈ endNames w t t') :
    namedPoint w a ∈
      (facet (polygonalInputOf w).V (curvePlane w t) (curvePlane w t')).extremePoints ℝ := by
  obtain ⟨t₁, -, t₂, -, -, -, -, h⟩ := ha
  exact h

/-! ## The records -/

/-- **The record of a patch**: the recorded labels; for each recorded site time, the labels whose
old cells meet its tile and the owner of the tile; for each pair of site times with a nondegenerate
facet, the names of the ends of the facet; the recorded names; the pairs of recorded names of equal
points; the conductances between recorded labels; the dyadic bins of the recorded names. -/
structure PatchRecord where
  /-- The labels of the cells meeting the window. -/
  labels : Finset ℤ
  /-- For each recorded site time: the labels meeting its tile and its owner. -/
  tiles : Finset (ℚ × Finset ℤ × ℤ)
  /-- For each pair of site times with a nondegenerate facet: the names of the facet ends. -/
  fans : Finset (ℚ × ℚ × Finset VName)
  /-- The recorded names. -/
  names : Finset VName
  /-- The pairs of recorded names of equal points. -/
  same : Finset (VName × VName)
  /-- The conductances between recorded labels, zeros included. -/
  cond : Finset (ℤ × ℤ × ℕ)
  /-- The dyadic bins of the recorded names. -/
  bins : Finset (VName × ℤ × ℤ)

instance : Countable PatchRecord := by
  have hinj : Function.Injective
      (fun r : PatchRecord => (r.labels, r.tiles, r.fans, r.names, r.same, r.cond, r.bins)) := by
    rintro ⟨_, _, _, _, _, _, _⟩ ⟨_, _, _, _, _, _, _⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
    rfl
  exact hinj.countable

namespace PatchRecord

variable (r : PatchRecord)

/-- The recorded names paired with `a` in `same`. -/
def sameAs (a : VName) : Finset VName :=
  open Classical in r.names.filter fun b => (a, b) ∈ r.same

/-- **The canonical name** of `a`: a recorded name paired with `a` in `same`, chosen as a function
of the set of these names. -/
def canon (a : VName) : VName := Classical.epsilon fun b => b ∈ r.sameAs a

/-- The faces of the cell `j` in the recorded names: for each recorded tile meeting the old cell
`j` and each of its facets with end names `E`, the fan triangle `{t} ∪ E` if `j` owns the tile, and
otherwise the facet `E` and the spokes `{t, a}` (`a ∈ E`). -/
def rawFaces (j : ℤ) : Set (Set VName) :=
  {F | ∃ t labs own t' E, (t, labs, own) ∈ r.tiles ∧ j ∈ labs ∧ (t, t', E) ∈ r.fans ∧
    (own = j ∧ F = insert (.inl t) (E : Set VName) ∨
      own ≠ j ∧ (F = (E : Set VName) ∨ ∃ a ∈ E, F = {.inl t, a}))}

/-- **The faces of the cell `j`** of a record, in canonical names. -/
def faces (j : ℤ) : Set (Set VName) := (fun F => r.canon '' F) '' r.rawFaces j

/-- **The canonical recorded names.** -/
def nameSet : Set VName := r.canon '' (r.names : Set VName)

end PatchRecord

variable (w) in
/-- The recorded names: the site times of `tileTimes` and the names of the facet ends. -/
def recordNames (R : ℕ) : Finset VName :=
  open Classical in
  (finsetOf (tileTimes w R)).image Sum.inl ∪
    (finsetOf (fanTimes w R)).biUnion fun tt => finsetOf (endNames w tt.1 tt.2)

/-- **The record of the patch of radius `R` at stage `n`** of the datum `w`. -/
def patchRecord (n R : ℕ) (w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) : PatchRecord :=
  open Classical in
  { labels := finsetOf (labelSet w R)
    tiles := (finsetOf (tileTimes w R)).image fun t =>
      (t, finsetOf ((polygonalInputOf w).labels (curvePlane w t)),
        (polygonalInputOf w).owner (curvePlane w t))
    fans := (finsetOf (fanTimes w R)).image fun tt => (tt.1, tt.2, finsetOf (endNames w tt.1 tt.2))
    names := recordNames w R
    same := (recordNames w R ×ˢ recordNames w R).filter fun ab =>
      namedPoint w ab.1 = namedPoint w ab.2
    cond := (finsetOf (labelSet w R) ×ˢ finsetOf (labelSet w R)).image fun ij =>
      (ij.1, ij.2, w.2 ij.1 ij.2)
    bins := (recordNames w R).image fun a =>
      (a, ⌊(2 : ℝ) ^ n * namedPoint w a 0⌋, ⌊(2 : ℝ) ^ n * namedPoint w a 1⌋) }

/-- **The record at stage `n`**: the records of the patches of radii `1, …, n` of a valid datum, and
`none` off the valid data. -/
def record (n : ℕ) (w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) : Option (Fin n → PatchRecord) :=
  open Classical in
  if UnitMeshValid w then some fun R : Fin n => patchRecord n ((R : ℕ) + 1) w else none

theorem record_of_valid (h : UnitMeshValid w) (n : ℕ) :
    record n w = some fun R : Fin n => patchRecord n ((R : ℕ) + 1) w := by
  unfold record
  rw [ite_eq_left h]

theorem record_of_not_valid (h : ¬ UnitMeshValid w) (n : ℕ) : record n w = none := by
  unfold record
  rw [ite_eq_right h]

theorem record_eq_none_iff {n : ℕ} : record n w = none ↔ ¬ UnitMeshValid w := by
  by_cases h : UnitMeshValid w
  · rw [record_of_valid h]
    simp [h]
  · rw [record_of_not_valid h]
    simp [h]

/-- Equal records at stage `n` have equal patch records for the radii `1 ≤ R ≤ n`. -/
theorem patchRecord_eq_of_record_eq {w' : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)} (hw : UnitMeshValid w)
    (hw' : UnitMeshValid w') {n : ℕ} (h : record n w = record n w') {R : ℕ} (hR : 1 ≤ R)
    (hRn : R ≤ n) : patchRecord n R w = patchRecord n R w' := by
  rw [record_of_valid hw, record_of_valid hw', Option.some.injEq] at h
  have h1 : patchRecord n (R - 1 + 1) w = patchRecord n (R - 1 + 1) w' :=
    congrFun h ⟨R - 1, by omega⟩
  rwa [Nat.sub_add_cancel hR] at h1

variable (w) in
/-- **The labels of the patch of radius `R`**: the cells meeting the closed ball of radius `R`. -/
def patchLabels (R : ℕ) : Finset ℤ := (patchRecord 0 R w).labels

variable (w) in
/-- **The canonical names of the patch of radius `R`.** -/
def patchNames (R : ℕ) : Set VName := (patchRecord 0 R w).nameSet

variable (w) in
/-- **The faces of the cells of the patch of radius `R`**, in canonical names. -/
def patchFaces (R : ℕ) : ℤ → Set (Set VName) := (patchRecord 0 R w).faces

theorem labels_patchRecord (n R : ℕ) : (patchRecord n R w).labels = patchLabels w R := rfl

theorem nameSet_patchRecord (n R : ℕ) : (patchRecord n R w).nameSet = patchNames w R := rfl

theorem faces_patchRecord (n R : ℕ) : (patchRecord n R w).faces = patchFaces w R := rfl

/-! ## The meaning of the records -/

theorem mem_patchLabels_iff (h : UnitMeshValid w) {R : ℕ} {j : ℤ} :
    j ∈ patchLabels w R ↔ ((polygonalInputOf w).cell j ∩ closedBall 0 R).Nonempty :=
  mem_finsetOf ((isValid_polygonalInputOf h).finite_cells_meeting 0 R)

theorem finite_patchNames (R : ℕ) : (patchNames w R).Finite :=
  (Finset.finite_toSet _).image _

theorem mem_cond_patchRecord {n R : ℕ} {i j : ℤ} {m : ℕ} :
    (i, j, m) ∈ (patchRecord n R w).cond ↔
      i ∈ patchLabels w R ∧ j ∈ patchLabels w R ∧ w.2 i j = m := by
  constructor
  · intro hm
    obtain ⟨⟨a, b⟩, hab, he⟩ := Finset.mem_image.1 hm
    rw [Finset.mem_product] at hab
    dsimp only at he
    rw [Prod.mk.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨hab.1, hab.2, rfl⟩
  · rintro ⟨hi, hj, rfl⟩
    exact Finset.mem_image.2 ⟨(i, j), Finset.mem_product.2 ⟨hi, hj⟩, rfl⟩

theorem mem_same_patchRecord {n R : ℕ} {a b : VName} :
    (a, b) ∈ (patchRecord n R w).same ↔
      a ∈ recordNames w R ∧ b ∈ recordNames w R ∧ namedPoint w a = namedPoint w b := by
  unfold patchRecord
  rw [Finset.mem_filter, Finset.mem_product, and_assoc]

theorem mem_bins_patchRecord {n R : ℕ} {a : VName} (ha : a ∈ recordNames w R) :
    (a, ⌊(2 : ℝ) ^ n * namedPoint w a 0⌋, ⌊(2 : ℝ) ^ n * namedPoint w a 1⌋) ∈
      (patchRecord n R w).bins :=
  Finset.mem_image_of_mem _ ha

/-- The site time of a recorded tile is a recorded name. -/
theorem inl_mem_recordNames_of_mem_tiles {n R : ℕ} {t : ℚ} {labs : Finset ℤ} {own : ℤ}
    (hT : (t, labs, own) ∈ (patchRecord n R w).tiles) : (.inl t : VName) ∈ recordNames w R := by
  obtain ⟨t₀, ht₀, he⟩ := Finset.mem_image.1 hT
  rw [Prod.mk.injEq] at he
  rw [← he.1]
  unfold recordNames
  exact Finset.mem_union.2 (Or.inl (Finset.mem_image_of_mem Sum.inl ht₀))

/-- The facet end names of a recorded fan pair are recorded names. -/
theorem mem_recordNames_of_mem_fans {n R : ℕ} {t t' : ℚ} {E : Finset VName} {a : VName}
    (hF : (t, t', E) ∈ (patchRecord n R w).fans) (ha : a ∈ E) : a ∈ recordNames w R := by
  classical
  obtain ⟨tt, htt, he⟩ := Finset.mem_image.1 hF
  rw [Prod.mk.injEq, Prod.mk.injEq] at he
  rw [← he.2.2] at ha
  unfold recordNames
  exact Finset.mem_union.2 (Or.inr (Finset.mem_biUnion.2 ⟨tt, htt, ha⟩))

/-- A recorded fan pair: the names of its facet ends name extreme points of its facet. -/
theorem exists_of_mem_fans {n R : ℕ} {t t' : ℚ} {E : Finset VName}
    (hF : (t, t', E) ∈ (patchRecord n R w).fans) :
    t ∈ tileTimes w R ∧ t' ∈ siteTimes w ∧
      IsFanPair (polygonalInputOf w).V (curvePlane w t) (curvePlane w t') ∧
      E = finsetOf (endNames w t t') := by
  classical
  obtain ⟨⟨t₁, t₂⟩, htt, he⟩ := Finset.mem_image.1 hF
  dsimp only at he
  rw [Prod.mk.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  obtain ⟨ht, ht', hpq⟩ := mem_of_mem_finsetOf htt
  exact ⟨ht, ht', hpq, rfl⟩

/-- **The canonical name** of a recorded name is a recorded name of the same point. -/
theorem canon_spec {n R : ℕ} {a : VName} (ha : a ∈ recordNames w R) :
    (patchRecord n R w).canon a ∈ recordNames w R ∧
      namedPoint w ((patchRecord n R w).canon a) = namedPoint w a := by
  have hmem : a ∈ (patchRecord n R w).sameAs a := by
    unfold PatchRecord.sameAs
    rw [Finset.mem_filter]
    exact ⟨ha, mem_same_patchRecord.2 ⟨ha, ha, rfl⟩⟩
  have hc : (patchRecord n R w).canon a ∈ (patchRecord n R w).sameAs a :=
    Classical.epsilon_spec ⟨a, hmem⟩
  unfold PatchRecord.sameAs at hc
  rw [Finset.mem_filter] at hc
  exact ⟨hc.1, (mem_same_patchRecord.1 hc.2).2.2.symm⟩

theorem image_canon {n R : ℕ} {F : Set VName} (hF : F ⊆ recordNames w R) :
    namedPoint w '' ((patchRecord n R w).canon '' F) = namedPoint w '' F := by
  rw [image_image]
  exact image_congr fun a ha => (canon_spec (hF ha)).2

/-- **The faces of a record**: their names are recorded names, and they name vertices of a single
fan triangle. -/
theorem rawFaces_spec {n R : ℕ} {j : ℤ} {F : Set VName}
    (hF : F ∈ (patchRecord n R w).rawFaces j) :
    F ⊆ recordNames w R ∧ ∃ t t', IsFanPair (polygonalInputOf w).V (curvePlane w t) (curvePlane w t') ∧
      namedPoint w '' F ⊆ fanVerts (polygonalInputOf w).V (curvePlane w t) (curvePlane w t') := by
  obtain ⟨t, labs, own, t', E, hT, -, hFa, hcase⟩ := hF
  have hinl := inl_mem_recordNames_of_mem_tiles hT
  have hE := fun a (ha : a ∈ E) => mem_recordNames_of_mem_fans hFa ha
  obtain ⟨-, -, hpq, rfl⟩ := exists_of_mem_fans hFa
  have hEsub : namedPoint w '' ((finsetOf (endNames w t t') : Finset VName) : Set VName) ⊆
      (facet (polygonalInputOf w).V (curvePlane w t) (curvePlane w t')).extremePoints ℝ := by
    rintro _ ⟨a, ha, rfl⟩
    exact namedPoint_mem_of_mem_endNames (mem_of_mem_finsetOf ha)
  refine ⟨?_, t, t', hpq, ?_⟩
  · rcases hcase with ⟨-, rfl⟩ | ⟨-, rfl | ⟨a, ha, rfl⟩⟩
    · exact insert_subset hinl fun a ha => hE a ha
    · exact fun a ha => hE a ha
    · exact insert_subset hinl (singleton_subset_iff.2 (hE a ha))
  · rcases hcase with ⟨-, rfl⟩ | ⟨-, rfl | ⟨a, ha, rfl⟩⟩
    · rw [image_insert_eq, namedPoint_inl]
      exact insert_subset_insert hEsub
    · exact hEsub.trans (subset_insert _ _)
    · rw [image_insert_eq, image_singleton, namedPoint_inl]
      exact insert_subset_insert (singleton_subset_iff.2 (hEsub (mem_image_of_mem _ ha)))

/-- **The cells of the recorded labels in recorded names**: for every recorded label `j`, the cell
of `j` is the union of the convex hulls of the named points of the faces of `j`. -/
theorem cell_eq_iUnion_rawFaces (h : UnitMeshValid w) {n R : ℕ} {j : ℤ}
    (hj : j ∈ (patchRecord n R w).labels) :
    (polygonalInputOf w).cell j =
      ⋃ F ∈ (patchRecord n R w).rawFaces j, convexHull ℝ (namedPoint w '' F) := by
  classical
  have hI := isValid_polygonalInputOf h
  have hV := h.isSiteSystem
  have hjL : j ∈ labelSet w R := mem_of_mem_finsetOf hj
  rw [PolygonalInput.cell_eq_iUnion hV j]
  refine Subset.antisymm (fun x hx => ?_) fun x hx => ?_
  · obtain ⟨p, hp, hx⟩ := mem_iUnion₂.1 hx
    obtain ⟨t, ht, rfl⟩ := mem_sites_iff.1 hp.1
    have htT : t ∈ tileTimes w R := ⟨ht, j, hjL, hp.2⟩
    have htile : (t, finsetOf ((polygonalInputOf w).labels (curvePlane w t)),
        (polygonalInputOf w).owner (curvePlane w t)) ∈ (patchRecord n R w).tiles :=
      Finset.mem_image.2 ⟨t, (mem_finsetOf (h.finite_tileTimes R)).2 htT, rfl⟩
    have hjlab : j ∈ finsetOf ((polygonalInputOf w).labels (curvePlane w t)) :=
      (mem_finsetOf (hI.finite_labels _)).2 hp.2
    have hfan : ∀ t' ∈ siteTimes w,
        IsFanPair (polygonalInputOf w).V (curvePlane w t) (curvePlane w t') →
        (t, t', finsetOf (endNames w t t')) ∈ (patchRecord n R w).fans := fun t' ht' hf =>
      Finset.mem_image.2 ⟨(t, t'), (mem_finsetOf (h.finite_fanTimes R)).2 ⟨htT, ht', hf⟩, rfl⟩
    have hE : ∀ t' ∈ siteTimes w,
        namedPoint w '' ((finsetOf (endNames w t t') : Finset VName) : Set VName) =
          (facet (polygonalInputOf w).V (curvePlane w t) (curvePlane w t')).extremePoints ℝ :=
      fun t' ht' => by rw [coe_finsetOf (h.finite_endNames t t'), image_endNames h ht ht']
    by_cases ho : (polygonalInputOf w).owner (curvePlane w t) = j
    · rw [ite_eq_left ho] at hx
      obtain ⟨q', hq', hxq⟩ := mem_iUnion₂.1 hx
      obtain ⟨t', ht', rfl⟩ := mem_sites_iff.1 hq'.2.1
      refine mem_iUnion₂.2 ⟨insert (.inl t) ((finsetOf (endNames w t t') : Finset VName) : Set VName),
        ⟨t, _, _, t', _, htile, hjlab, hfan t' ht' hq', Or.inl ⟨ho, rfl⟩⟩, ?_⟩
      rw [hV.fan_eq_convexHull_fanVerts hp.1 hq'.2.1] at hxq
      rw [image_insert_eq, namedPoint_inl, hE t' ht']
      exact hxq
    · rw [ite_eq_right ho] at hx
      obtain ⟨q', hq', hxq⟩ := mem_iUnion₂.1 hx
      obtain ⟨t', ht', rfl⟩ := mem_sites_iff.1 hq'.2.1
      rcases hxq with hxf | hxs
      · refine mem_iUnion₂.2 ⟨((finsetOf (endNames w t t') : Finset VName) : Set VName),
          ⟨t, _, _, t', _, htile, hjlab, hfan t' ht' hq', Or.inr ⟨ho, Or.inl rfl⟩⟩, ?_⟩
        rw [hE t' ht', hV.convexHull_extremePoints_facet hp.1 hq'.2.1]
        exact hxf
      · obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.1 hxs
        rw [← hE t' ht'] at hv
        obtain ⟨a, ha, rfl⟩ := hv
        refine mem_iUnion₂.2 ⟨{.inl t, a},
          ⟨t, _, _, t', _, htile, hjlab, hfan t' ht' hq', Or.inr ⟨ho, Or.inr ⟨a, ha, rfl⟩⟩⟩, ?_⟩
        rw [image_insert_eq, image_singleton, namedPoint_inl, convexHull_pair]
        exact hxv
  · obtain ⟨F, ⟨t₀, labs, own, t₀', E, hT, hjl, hF, hcase⟩, hx⟩ := mem_iUnion₂.1 hx
    obtain ⟨t, -, he⟩ := Finset.mem_image.1 hT
    rw [Prod.mk.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    obtain ⟨ht, ht', hpq, rfl⟩ := exists_of_mem_fans hF
    have hpV : curvePlane w t ∈ (polygonalInputOf w).V := mem_sites_iff.2 ⟨t, ht.1, rfl⟩
    have hjt : j ∈ (polygonalInputOf w).labels (curvePlane w t) := mem_of_mem_finsetOf hjl
    have hEsub : namedPoint w '' ((finsetOf (endNames w t t₀') : Finset VName) : Set VName) ⊆
        (facet (polygonalInputOf w).V (curvePlane w t) (curvePlane w t₀')).extremePoints ℝ := by
      rintro _ ⟨a, ha, rfl⟩
      exact namedPoint_mem_of_mem_endNames (mem_of_mem_finsetOf ha)
    refine mem_iUnion₂.2 ⟨curvePlane w t, ⟨hpV, hjt⟩, ?_⟩
    rcases hcase with ⟨ho, rfl⟩ | ⟨ho, rfl | ⟨a, ha, rfl⟩⟩
    · rw [ite_eq_left ho]
      refine mem_iUnion₂.2 ⟨curvePlane w t₀', hpq, ?_⟩
      rw [hV.fan_eq_convexHull_fanVerts hpV hpq.2.1]
      refine convexHull_mono ?_ hx
      rw [image_insert_eq, namedPoint_inl]
      exact insert_subset_insert hEsub
    · rw [ite_eq_right ho]
      refine mem_iUnion₂.2 ⟨curvePlane w t₀', hpq, Or.inl ?_⟩
      rw [← hV.convexHull_extremePoints_facet hpV hpq.2.1]
      exact convexHull_mono hEsub hx
    · rw [ite_eq_right ho]
      refine mem_iUnion₂.2 ⟨curvePlane w t₀', hpq, Or.inr (mem_iUnion₂.2 ⟨namedPoint w a,
        hEsub (mem_image_of_mem _ ha), ?_⟩)⟩
      rw [image_insert_eq, image_singleton, namedPoint_inl, convexHull_pair] at hx
      exact hx

/-- **The cells of the patch in canonical names**: for every label `j` of the patch of radius `R`,
the cell of `j` is the union of the convex hulls of the named points of the faces of `j`. -/
theorem cell_eq_iUnion_patchFaces (h : UnitMeshValid w) {R : ℕ} {j : ℤ}
    (hj : j ∈ patchLabels w R) :
    (polygonalInputOf w).cell j = ⋃ F ∈ patchFaces w R j, convexHull ℝ (namedPoint w '' F) := by
  rw [cell_eq_iUnion_rawFaces h (n := 0) hj]
  unfold patchFaces PatchRecord.faces
  rw [biUnion_image]
  refine iUnion₂_congr fun F hF => ?_
  rw [image_canon (rawFaces_spec hF).1]

/-- **The faces of the patch**: their names are canonical names of the patch, and they name
vertices of a single fan triangle. -/
theorem face_spec (h : UnitMeshValid w) {R : ℕ} {j : ℤ} {F : Set VName}
    (hF : F ∈ patchFaces w R j) :
    F ⊆ patchNames w R ∧ ∃ i : FanIndex (polygonalInputOf w).V,
      namedPoint w '' F ⊆ {fanTri _ i 0, fanTri _ i 1, fanTri _ i 2} := by
  obtain ⟨F₀, hF₀, rfl⟩ := hF
  obtain ⟨hsub, t, t', hpq, him⟩ := rawFaces_spec hF₀
  refine ⟨image_mono hsub, ⟨(curvePlane w t, curvePlane w t'), hpq⟩, ?_⟩
  rw [image_canon hsub, ← h.isSiteSystem.fanVerts_eq ⟨(curvePlane w t, curvePlane w t'), hpq⟩]
  exact him

/-- **The canonical names name distinct points.** -/
theorem injOn_namedPoint_patchNames (R : ℕ) : (patchNames w R).InjOn (namedPoint w) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
  have ha' : a ∈ recordNames w R := ha
  have hb' : b ∈ recordNames w R := hb
  have hab' : namedPoint w a = namedPoint w b := by
    rw [← (canon_spec (n := 0) ha').2, ← (canon_spec (n := 0) hb').2]
    exact hab
  have hs : (patchRecord 0 R w).sameAs a = (patchRecord 0 R w).sameAs b := by
    ext c
    unfold PatchRecord.sameAs
    rw [Finset.mem_filter, Finset.mem_filter, mem_same_patchRecord, mem_same_patchRecord, hab']
    exact ⟨fun h => ⟨h.1, hb', h.2.2⟩, fun h => ⟨h.1, ha', h.2.2⟩⟩
  unfold PatchRecord.canon
  rw [hs]

/-! ## The dyadic bins -/

theorem abs_sub_lt_of_floor_mul_eq {c a b : ℝ} (hc : 0 < c) (h : ⌊c * a⌋ = ⌊c * b⌋) :
    |a - b| < c⁻¹ := by
  have h1 := Int.abs_sub_lt_one_of_floor_eq_floor h
  rw [← mul_sub, abs_mul, abs_of_pos hc] at h1
  rw [inv_eq_one_div, lt_div_iff₀' hc]
  exact h1

/-- Two points of the plane with the same dyadic bin of side `2^{-n}` are within `√2 · 2^{-n}`. -/
theorem dist_le_of_floor_eq {n : ℕ} {x y : Plane} (h0 : ⌊(2 : ℝ) ^ n * x 0⌋ = ⌊(2 : ℝ) ^ n * y 0⌋)
    (h1 : ⌊(2 : ℝ) ^ n * x 1⌋ = ⌊(2 : ℝ) ^ n * y 1⌋) :
    dist x y ≤ Real.sqrt 2 * ((2 : ℝ) ^ n)⁻¹ := by
  have hc : (0 : ℝ) < 2 ^ n := by positivity
  have e0 := abs_sub_lt_of_floor_mul_eq hc h0
  have e1 := abs_sub_lt_of_floor_mul_eq hc h1
  have hε : (0 : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹ := inv_nonneg.2 hc.le
  have a0 : (x 0 - y 0) ^ 2 ≤ ((2 : ℝ) ^ n)⁻¹ * ((2 : ℝ) ^ n)⁻¹ := by
    rw [← sq_abs, sq]
    exact mul_self_le_mul_self (abs_nonneg _) e0.le
  have a1 : (x 1 - y 1) ^ 2 ≤ ((2 : ℝ) ^ n)⁻¹ * ((2 : ℝ) ^ n)⁻¹ := by
    rw [← sq_abs, sq]
    exact mul_self_le_mul_self (abs_nonneg _) e1.le
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]
  calc Real.sqrt ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2)
      ≤ Real.sqrt (2 * (((2 : ℝ) ^ n)⁻¹ * ((2 : ℝ) ^ n)⁻¹)) := Real.sqrt_le_sqrt (by linarith)
    _ = Real.sqrt 2 * ((2 : ℝ) ^ n)⁻¹ := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul_self hε]

/-- **Equal bins give close points**: if a name has the same dyadic bin in the records of two data
at stage `n`, the points it names are within `√2 · 2^{-n}` of each other. -/
theorem dist_namedPoint_le_of_mem_bins {w' : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)} {n R R' : ℕ} {a : VName}
    {k : ℤ × ℤ} (h : (a, k) ∈ (patchRecord n R w).bins) (h' : (a, k) ∈ (patchRecord n R' w').bins) :
    dist (namedPoint w a) (namedPoint w' a) ≤ Real.sqrt 2 * ((2 : ℝ) ^ n)⁻¹ := by
  obtain ⟨b, -, hb⟩ := Finset.mem_image.1 h
  obtain ⟨b', -, hb'⟩ := Finset.mem_image.1 h'
  rw [Prod.mk.injEq] at hb hb'
  obtain ⟨rfl, hk⟩ := hb
  obtain ⟨hbb, hk'⟩ := hb'
  subst hbb
  rw [← hk', Prod.mk.injEq] at hk
  exact dist_le_of_floor_eq hk.1 hk.2

/-! ## Equal patch records -/

/-- **Equal patch records give close named points**: within `2 · 2^{-n}`. -/
theorem dist_namedPoint_le_of_patchRecord_eq {w' : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)} {n R : ℕ}
    (he : patchRecord n R w = patchRecord n R w') {a : VName} (ha : a ∈ patchNames w R) :
    dist (namedPoint w a) (namedPoint w' a) ≤ 2 * (1 / 2) ^ n := by
  obtain ⟨b, hb, rfl⟩ := ha
  have hc := (canon_spec (n := 0) (hb : b ∈ recordNames w R)).1
  have h1 := mem_bins_patchRecord (n := n) hc
  have h2 := h1
  rw [he] at h2
  have hs2 : Real.sqrt 2 ≤ 2 := by
    have h4 : Real.sqrt 2 ≤ Real.sqrt (2 * 2) := Real.sqrt_le_sqrt (by norm_num)
    rwa [Real.sqrt_mul_self (by norm_num)] at h4
  calc dist _ _ ≤ Real.sqrt 2 * ((2 : ℝ) ^ n)⁻¹ := dist_namedPoint_le_of_mem_bins h1 h2
    _ ≤ 2 * (1 / 2) ^ n := by
      rw [one_div_pow, one_div]
      exact mul_le_mul_of_nonneg_right hs2 (by positivity)

/-- **Equal patch records give equal conductances** between the labels of the patch. -/
theorem cond_eq_of_patchRecord_eq {w' : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)} {n R : ℕ}
    (he : patchRecord n R w = patchRecord n R w') {j k : ℤ} (hj : j ∈ patchLabels w R)
    (hk : k ∈ patchLabels w R) : w.2 j k = w'.2 j k := by
  have h1 : (j, k, w.2 j k) ∈ (patchRecord n R w).cond := mem_cond_patchRecord.2 ⟨hj, hk, rfl⟩
  rw [he] at h1
  exact (mem_cond_patchRecord.1 h1).2.2.symm

theorem patchLabels_eq_of_patchRecord_eq {w' : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)} {n R : ℕ}
    (he : patchRecord n R w = patchRecord n R w') : patchLabels w' R = patchLabels w R := by
  rw [← labels_patchRecord n R, ← labels_patchRecord (w := w) n R, he]

theorem patchFaces_eq_of_patchRecord_eq {w' : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)} {n R : ℕ}
    (he : patchRecord n R w = patchRecord n R w') : patchFaces w' R = patchFaces w R := by
  rw [← faces_patchRecord n R, ← faces_patchRecord (w := w) n R, he]

/-- **Equal records give matched patches**: if two valid data have the same record at stage `n`,
then for `1 ≤ R ≤ n` their patches of radius `R` are matched, with the labels, canonical names and
faces of the patch of `w`, the named points of `w` and of `w'`, and displacement bound
`2 · 2^{-n}`. -/
theorem patchMatch_of_record_eq {w' : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)} (hw : UnitMeshValid w)
    (hw' : UnitMeshValid w') {n : ℕ} (h : record n w = record n w') {R : ℕ} (hR : 1 ≤ R)
    (hRn : R ≤ n) :
    PatchMatch w w' R (2 * (1 / 2) ^ n) (patchLabels w R) (patchNames w R) (namedPoint w)
      (namedPoint w') (patchFaces w R) := by
  have he := patchRecord_eq_of_record_eq hw hw' h hR hRn
  have hL := patchLabels_eq_of_patchRecord_eq he
  have hΦ := patchFaces_eq_of_patchRecord_eq he
  refine ⟨hw, hw', fun j hj => (mem_patchLabels_iff hw).2 hj, fun j hj => ?_,
    fun j hj => cell_eq_iUnion_patchFaces hw hj, fun j hj => ?_, fun j _ F hF => face_spec hw hF,
    injOn_namedPoint_patchNames R, fun a ha => dist_namedPoint_le_of_patchRecord_eq he ha,
    fun j hj k hk => cond_eq_of_patchRecord_eq he hj hk⟩
  · rw [← hL]
    exact (mem_patchLabels_iff hw').2 hj
  · rw [← hΦ]
    refine cell_eq_iUnion_patchFaces hw' ?_
    rw [hL]
    exact hj

end MatedCRT.ZeroConePolygonal
