import MatedCRT.FirstPass.Derived.ZeroConePolygonalGMS
import MatedCRT.FirstPass.Derived.ZeroConePolygonalScale
import MatedCRT.FirstPass.Derived.ZeroConePolygonalSites
import MatedCRT.Defs.Map

/-!
# The polygonal input of a unit-mesh weighted datum

A unit-mesh weighted datum is a pair `w = (η, m)` of a continuous curve `η : C(ℝ, ℂ)` and edge counts
`m : ℤ → ℤ → ℕ`. Its old cells are `K_j = η([j - 1, j])` and its vertices are `v_j = η(j)`, both
transported to the plane by `Complex.orthonormalBasisOneI.repr`.

* `unitCell w j`, `unitVertex w j`, `curvePlane w`: the old cells, the vertices and the curve in the plane.
* `UnitMeshValid w`: the geometric hypotheses on the old cells and the point connectivity of the labels.
  (Compactness and connectedness of the cells are not hypotheses: they are images of `[j - 1, j]`
  under a continuous map.)
* `polygonalInputOf w`: the polygonal input with scale function `scaleFun`, weights `weight` and the
  dyadic sites of the curve.
* `isValid_polygonalInputOf`: under `UnitMeshValid w` the input is valid.
* `carriesUnitMeshWalk_polygonalInputOf`: the polygonal cells carry the walk of `w`: the body of
  `CarriesUnitMeshWalk w ((polygonalInputOf w).toGMS _)`.
* `cell_ratio_unitCell_le`, `cell_ratio_of_notMem_shared_le`: the pointwise moment bound
  `(diam C_j)² / |C_j| ∑_k (m_jk + m_jk⁻¹) ≤ 8 e_i` for the new cell `C_j` of a point of the old cell `K_i`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology Relation

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open ReflectedGMS

/-- The curve `η` of a datum, in the plane. -/
def curvePlane (w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) : ℝ → Plane :=
  fun t => Complex.orthonormalBasisOneI.repr (w.1 t)

/-- **The old cell** `K_j = η([j - 1, j])` of a datum, in the plane. -/
def unitCell (w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) (j : ℤ) : Set Plane :=
  Complex.orthonormalBasisOneI.repr '' MatedCRT.cell 1 w.1 j

/-- **The vertex** `v_j = η(j)` of a datum, in the plane. -/
def unitVertex (w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) (j : ℤ) : Plane :=
  Complex.orthonormalBasisOneI.repr (MatedCRT.vertexPoint 1 w.1 j)

variable (w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ))

theorem continuous_curvePlane : Continuous (curvePlane w) :=
  Complex.orthonormalBasisOneI.repr.continuous.comp w.1.continuous

theorem timeCell_curvePlane (j : ℤ) : timeCell (curvePlane w) j = unitCell w j := by
  simp only [timeCell, unitCell, MatedCRT.cell, one_mul, Set.image_image]
  rfl

theorem unitVertex_eq (j : ℤ) : unitVertex w j = curvePlane w j := by
  simp [unitVertex, MatedCRT.vertexPoint, curvePlane]

theorem isCompact_unitCell (j : ℤ) : IsCompact (unitCell w j) :=
  (isCompact_Icc.image w.1.continuous).image Complex.orthonormalBasisOneI.repr.continuous

theorem isPreconnected_unitCell (j : ℤ) : IsPreconnected (unitCell w j) :=
  (isPreconnected_Icc.image _ w.1.continuous.continuousOn).image _
    Complex.orthonormalBasisOneI.repr.continuous.continuousOn

theorem unitVertex_mem_unitCell (j : ℤ) : unitVertex w j ∈ unitCell w j :=
  mem_image_of_mem _ (mem_image_of_mem _ ⟨by simp, by simp⟩)

/-- **The hypotheses on a unit-mesh datum**: the old cells have positive area, are locally finite, cover the
plane and overlap in null sets; the edge counts are symmetric with zero diagonal and positive only between
cells that meet; the old cells through a point are joined by a chain of positive counts between cells
through that point. -/
structure UnitMeshValid : Prop where
  volume_pos : ∀ j, 0 < volume (unitCell w j)
  lf : ∀ A : Set Plane, IsCompact A → {j | (unitCell w j ∩ A).Nonempty}.Finite
  cover : ∀ z, ∃ j, z ∈ unitCell w j
  volume_inter : ∀ i j, i ≠ j → volume (unitCell w i ∩ unitCell w j) = 0
  m_symm : ∀ i j, w.2 i j = w.2 j i
  m_diag : ∀ j, w.2 j j = 0
  m_inter : ∀ i j, 0 < w.2 i j → (unitCell w i ∩ unitCell w j).Nonempty
  pt : ∀ z i j, z ∈ unitCell w i → z ∈ unitCell w j →
    ReflTransGen (fun a b => 0 < w.2 a b ∧ z ∈ unitCell w a ∧ z ∈ unitCell w b) i j

/-- **The polygonal input of a datum**: old cells `K_j = η([j - 1, j])`, counts `m`, vertices `η(j)`, scale
function `scaleFun`, weights `weight` and the dyadic sites of the curve for that scale. -/
def polygonalInputOf : PolygonalInput where
  K := unitCell w
  m := w.2
  v := unitVertex w
  V := dyadicSites (curvePlane w) (scaleFun (unitCell w) w.2)
  r := scaleFun (unitCell w) w.2
  e := weight (unitCell w) w.2

variable {w}

theorem UnitMeshValid.oldCells (h : UnitMeshValid w) : OldCells (unitCell w) w.2 where
  compact := isCompact_unitCell w
  volume_pos := h.volume_pos
  lf := h.lf
  cover := h.cover
  volume_inter := h.volume_inter
  m_symm := h.m_symm
  m_inter := h.m_inter

theorem UnitMeshValid.isSiteSystem (h : UnitMeshValid w) :
    IsSiteSystem (polygonalInputOf w).V (polygonalInputOf w).r :=
  isSiteSystem_dyadicSites (q := curvePlane w) (s := scaleFun (unitCell w) w.2)
    (continuous_curvePlane w) (scaleFun_lip (unitCell w) w.2) (scaleFun_pos h.oldCells)
    (fun z => by
      obtain ⟨j, hj⟩ := h.cover z
      exact ⟨j, by rw [timeCell_curvePlane]; exact hj⟩)
    (fun A hA => by
      simpa only [timeCell_curvePlane] using h.lf A hA)

/-- **The polygonal input of a valid datum is valid.** -/
theorem isValid_polygonalInputOf (h : UnitMeshValid w) : (polygonalInputOf w).IsValid where
  site := h.isSiteSystem
  compact := isCompact_unitCell w
  conn := isPreconnected_unitCell w
  lf := h.lf
  cover := h.cover
  pt := h.pt
  m_symm := h.m_symm
  m_diag := h.m_diag
  m_inter := h.m_inter
  vsite j := by
    show unitVertex w j ∈ dyadicSites (curvePlane w) (scaleFun (unitCell w) w.2)
    rw [unitVertex_eq]
    exact mem_dyadicSites j
  vmem := unitVertex_mem_unitCell w
  own j := PolygonalInput.exists_owner_eq (I := polygonalInputOf w) h.oldCells rfl h.isSiteSystem j

/-- **The polygonal cells carry the walk of the datum**: the body of
`CarriesUnitMeshWalk w ((polygonalInputOf w).toGMS _)`. The labels `ℤ` are in bijection with the cells of
the polygonal configuration, the conductance between the cells of `a` and `b` is the edge count `m a b`,
the vertex `η(j)` lies in the `j`-th cell, and every point `z` of `η([j - 1, j])` lies in a cell within its
diameter of a point of the `j`-th cell. -/
theorem carriesUnitMeshWalk_polygonalInputOf (h : UnitMeshValid w) :
    ∃ e : ℤ ≃ ((polygonalInputOf w).toGMS (isValid_polygonalInputOf h)).1.cells,
      (∀ a b : ℤ, ((polygonalInputOf w).toGMS (isValid_polygonalInputOf h)).1.c (e a) (e b) =
        (w.2 a b : ℝ)) ∧
      (∀ j : ℤ, Complex.orthonormalBasisOneI.repr (MatedCRT.vertexPoint 1 w.1 j) ∈
        ((e j : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane)) ∧
      ∀ j : ℤ, ∀ z ∈ MatedCRT.cell 1 w.1 j,
        ∃ K : ((polygonalInputOf w).toGMS (isValid_polygonalInputOf h)).1.cells,
          Complex.orthonormalBasisOneI.repr z ∈
            ((K : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane) ∧
          ∃ y ∈ ((e j : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane),
            dist (Complex.orthonormalBasisOneI.repr z) y ≤
              Metric.diam ((K : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane) := by
  obtain ⟨e, hc, hv, hn⟩ := (polygonalInputOf w).exists_equiv_cells (isValid_polygonalInputOf h)
  exact ⟨e, hc, hv, fun j z hz => hn j _ (mem_image_of_mem _ hz)⟩

/-- **The pointwise moment bound** (answer, lines 35-38): if a point `x` of the old cell `K_i` lies in the
Voronoi tile of the site `p`, then the polygonal cell `C_j` of the owner `j` of that tile satisfies
`(diam C_j)² / |C_j| ∑_k (m_jk + m_jk⁻¹) ≤ 8 e_i`. -/
theorem cell_ratio_unitCell_le (h : UnitMeshValid w) {i : ℤ} {p x : Plane} (hxi : x ∈ unitCell w i)
    (hxp : x ∈ tile (polygonalInputOf w).V p) :
    diam ((polygonalInputOf w).cell ((polygonalInputOf w).owner p)) ^ 2 /
        (volume ((polygonalInputOf w).cell ((polygonalInputOf w).owner p))).toReal *
      ∑ᶠ k ∈ {k : ℤ | 0 < w.2 ((polygonalInputOf w).owner p) k},
        ((w.2 ((polygonalInputOf w).owner p) k : ℝ) +
          ((w.2 ((polygonalInputOf w).owner p) k : ℝ))⁻¹) ≤
      8 * weight (unitCell w) w.2 i :=
  PolygonalInput.cell_ratio_owner_le (I := polygonalInputOf w) h.oldCells rfl rfl h.isSiteSystem
    hxi hxp

/-- **The pointwise moment bound for the new cell of a point off the shared pieces**: if `x ∈ K_i` lies in
the polygonal cell `C_j` and in no shared piece of a tile of a site containing it, then
`(diam C_j)² / |C_j| ∑_k (m_jk + m_jk⁻¹) ≤ 8 e_i`. -/
theorem cell_ratio_of_notMem_shared_le (h : UnitMeshValid w) {i j : ℤ} {x : Plane}
    (hxi : x ∈ unitCell w i) (hxj : x ∈ (polygonalInputOf w).cell j)
    (hxs : ∀ p ∈ (polygonalInputOf w).V, x ∈ tile (polygonalInputOf w).V p →
      x ∉ shared (polygonalInputOf w).V p) :
    diam ((polygonalInputOf w).cell j) ^ 2 / (volume ((polygonalInputOf w).cell j)).toReal *
      ∑ᶠ k ∈ {k : ℤ | 0 < w.2 j k}, ((w.2 j k : ℝ) + ((w.2 j k : ℝ))⁻¹) ≤
      8 * weight (unitCell w) w.2 i := by
  obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.1 hxj
  have hown : (polygonalInputOf w).owner q = j := by
    by_contra hne
    rw [PolygonalInput.piece_of_ne hne] at hxq
    exact hxs q hq.1 (shared_subset_tile _ q hxq) hxq
  have := cell_ratio_unitCell_le h hxi (PolygonalInput.piece_subset_tile q j hxq)
  rwa [hown] at this

end MatedCRT.ZeroConePolygonal
