import MatedCRT.FirstPass.Derived.ZeroConePolygonalData
import LatticeProb.Prob.CellConfigIntegerConductanceMoment

/-!
# The polygonal configuration of a unit-mesh datum

The polygonal cells `C_j` of a valid unit-mesh datum `w = (η, m)` form a cell configuration of
Gwynne–Miller–Sheffield (arXiv:1807.07515, Definition 1.15) carrying the walk of `w` (the construction of the
polygonal configuration in the proof of Lemma 3.5 of Gwynne–Miller–Sheffield, arXiv:1705.11161). This file
packages it as a map from data to the GMS space, with a default point `H₀` off the valid data.

* `polygonalConfig H₀ w`: the GMS configuration of the polygonal cells of `w` if `UnitMeshValid w`, and `H₀`
  otherwise.
* `polygonalConfig_of_valid`, `polygonalConfig_of_not_valid`: the two branches.
* `lineConnected_polygonalConfig`: for valid data the configuration is connected along lines.
* `carriesUnitMeshWalk_body_polygonalConfig`: for valid data the cells carry the walk of `w` (the body of
  `CarriesUnitMeshWalk w (polygonalConfig H₀ w)`).
* `rootCell H`: a cell of `H` containing the origin with the least `diam²/Area · π` (the cell `H₀` of the
  finite-expectation hypothesis (1.5) of arXiv:1807.07515, chosen among the finitely many cells containing `0`).
* `rootDensity_polygonalConfig_le`, `piStar_polygonalConfig_le_pi`: for valid data and an old cell `K_i`
  containing the origin, `diam²/Area · π` of the root cell is at most `8 e_i` (the pointwise moment bound
  `cell_ratio_unitCell_le` at a Voronoi tile containing the origin), and `π* ≤ π` (integer conductances).
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open ReflectedGMS ReflectedGMS.GMS

open Classical in
/-- **The polygonal configuration of a unit-mesh datum**: the GMS configuration of the polygonal cells of `w`
when `w` is a valid datum, and the default point `H₀` otherwise. -/
def polygonalConfig (H₀ : GMSSpace) (w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) : GMSSpace :=
  if h : UnitMeshValid w then (polygonalInputOf w).toGMS (isValid_polygonalInputOf h) else H₀

variable {H₀ : GMSSpace} {w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)}

theorem polygonalConfig_of_valid (h : UnitMeshValid w) :
    polygonalConfig H₀ w = (polygonalInputOf w).toGMS (isValid_polygonalInputOf h) := by
  rw [polygonalConfig, dite_eq_left h]

theorem polygonalConfig_of_not_valid (h : ¬ UnitMeshValid w) : polygonalConfig H₀ w = H₀ := by
  rw [polygonalConfig, dite_eq_right h]

/-- **The polygonal configuration of a valid datum is connected along lines.** -/
theorem lineConnected_polygonalConfig (h : UnitMeshValid w) : (polygonalConfig H₀ w).1.LineConnected := by
  rw [polygonalConfig_of_valid h]
  exact (polygonalInputOf w).lineConnected (isValid_polygonalInputOf h)

/-- **The polygonal configuration of a valid datum carries its walk**: the body of
`CarriesUnitMeshWalk w (polygonalConfig H₀ w)`. The labels `ℤ` are in bijection with the cells, the
conductance between the cells of `a` and `b` is the edge count `m a b`, the vertex `η(j)` lies in the `j`-th
cell, and every point `z` of `η([j - 1, j])` lies in a cell within its diameter of a point of the `j`-th cell. -/
theorem carriesUnitMeshWalk_body_polygonalConfig (h : UnitMeshValid w) :
    ∃ e : ℤ ≃ (polygonalConfig H₀ w).1.cells,
      (∀ a b : ℤ, (polygonalConfig H₀ w).1.c (e a) (e b) = (w.2 a b : ℝ)) ∧
      (∀ j : ℤ, Complex.orthonormalBasisOneI.repr (MatedCRT.vertexPoint 1 w.1 j) ∈
        ((e j : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane)) ∧
      ∀ j : ℤ, ∀ z ∈ MatedCRT.cell 1 w.1 j,
        ∃ K : (polygonalConfig H₀ w).1.cells,
          Complex.orthonormalBasisOneI.repr z ∈
            ((K : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane) ∧
          ∃ y ∈ ((e j : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane),
            dist (Complex.orthonormalBasisOneI.repr z) y ≤
              Metric.diam ((K : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane) := by
  rw [polygonalConfig_of_valid h]
  exact carriesUnitMeshWalk_polygonalInputOf h

/-! ## The root cell -/

/-- The quantity `diam(K)² / Area(K) · π(K)` of the finite-expectation hypothesis for a cell `K` of `H`. -/
def rootDensity (H : GMSSpace) (K : Cell) : ℝ :=
  Metric.diam (K : Set Plane) ^ 2 / CellConfig.area K * H.1.pi K

theorem exists_rootCell (H : GMSSpace) :
    ∃ K ∈ H.1.restrict {0}, ∀ K' ∈ H.1.restrict {0}, rootDensity H K ≤ rootDensity H K' := by
  refine Set.exists_min_image (H.1.restrict {0}) (rootDensity H)
    (CellConfig.finite_restrict_of_isCompact H.2 isCompact_singleton) ?_
  have h0 : (0 : Plane) ∈ ⋃ K ∈ H.1.cells, (K : Set Plane) := by
    rw [H.2.iUnion_eq_univ]
    exact mem_univ _
  obtain ⟨K, hK, h0K⟩ := mem_iUnion₂.1 h0
  exact ⟨K, hK, 0, h0K, mem_singleton _⟩

/-- **The root cell** of a configuration: a cell containing the origin with the least
`diam(K)² / Area(K) · π(K)` (only finitely many cells contain the origin). -/
def rootCell (H : GMSSpace) : Cell := (exists_rootCell H).choose

theorem rootCell_mem (H : GMSSpace) :
    rootCell H ∈ H.1.cells ∧ (0 : Plane) ∈ (rootCell H : Set Plane) := by
  obtain ⟨hK, hz⟩ := (exists_rootCell H).choose_spec.1
  exact ⟨hK, Set.inter_singleton_nonempty.1 hz⟩

theorem rootDensity_rootCell_le (H : GMSSpace) {K : Cell} (hK : K ∈ H.1.cells)
    (h0 : (0 : Plane) ∈ (K : Set Plane)) : rootDensity H (rootCell H) ≤ rootDensity H K :=
  (exists_rootCell H).choose_spec.2 K ⟨hK, Set.inter_singleton_nonempty.2 h0⟩

/-- A valid datum has finitely many positive counts from each label. -/
theorem UnitMeshValid.finite_setOf_pos (h : UnitMeshValid w) (j : ℤ) : {k : ℤ | 0 < w.2 j k}.Finite :=
  (h.lf (unitCell w j) (isCompact_unitCell w j)).subset fun k hk => by
    obtain ⟨x, hxj, hxk⟩ := h.m_inter j k hk
    exact ⟨x, hxk, hxj⟩

/-- In the polygonal configuration of a valid datum, `π(C_j) = ∑_k m_jk`. -/
theorem pi_toGMS_cellNC (h : UnitMeshValid w) (j : ℤ) :
    ((polygonalInputOf w).toGMS (isValid_polygonalInputOf h)).1.pi ((polygonalInputOf w).cellNC j) =
      ∑' k : ℤ, (w.2 j k : ℝ) := by
  have hI := isValid_polygonalInputOf h
  let e : ℤ ≃ ((polygonalInputOf w).toGMS hI).1.cells := Equiv.ofInjective _ hI.cellNC_injective
  calc ((polygonalInputOf w).toGMS (isValid_polygonalInputOf h)).1.pi ((polygonalInputOf w).cellNC j)
      = ∑' k : ℤ, ((polygonalInputOf w).toGMS hI).1.c ((polygonalInputOf w).cellNC j) (e k) :=
        (e.tsum_eq fun K' => ((polygonalInputOf w).toGMS hI).1.c ((polygonalInputOf w).cellNC j) K').symm
    _ = ∑' k : ℤ, (w.2 j k : ℝ) := tsum_congr fun k => hI.cellConfig_c j k

/-- **The root density of the polygonal configuration** (answer, lines 35-38): for a valid datum and a label `i`
whose old cell `K_i` contains the origin, `diam²/Area · π` of the root cell is at most `8 e_i`. The origin lies
in a Voronoi tile, which lies in the polygonal cell `C_j` of its owner `j`, and `cell_ratio_unitCell_le` bounds
`diam(C_j)²/|C_j| · ∑_k (m_jk + m_jk⁻¹) ≥ diam(C_j)²/|C_j| · π(C_j)`. -/
theorem rootDensity_polygonalConfig_le (h : UnitMeshValid w) {i : ℤ} (hi : (0 : Plane) ∈ unitCell w i) :
    rootDensity (polygonalConfig H₀ w) (rootCell (polygonalConfig H₀ w)) ≤
      8 * weight (unitCell w) w.2 i := by
  have hI := isValid_polygonalInputOf h
  obtain ⟨p, hpV, h0p⟩ := hI.site.exists_mem_tile 0
  have h0j : (0 : Plane) ∈ (polygonalInputOf w).cell ((polygonalInputOf w).owner p) :=
    hI.tile_subset_cell_owner hpV h0p
  rw [polygonalConfig_of_valid h]
  refine le_trans (rootDensity_rootCell_le ((polygonalInputOf w).toGMS hI)
    (K := (polygonalInputOf w).cellNC ((polygonalInputOf w).owner p)) ⟨_, rfl⟩
    (by rw [hI.coe_cellNC]; exact h0j)) ?_
  have hS := h.finite_setOf_pos ((polygonalInputOf w).owner p)
  have hvan : ∀ k ∉ hS.toFinset, (w.2 ((polygonalInputOf w).owner p) k : ℝ) = 0 := by
    intro k hk
    have hk' : ¬ 0 < w.2 ((polygonalInputOf w).owner p) k := fun hpos => hk (hS.mem_toFinset.2 hpos)
    have hz : w.2 ((polygonalInputOf w).owner p) k = 0 := by omega
    rw [hz, Nat.cast_zero]
  have hpi : ∑' k : ℤ, (w.2 ((polygonalInputOf w).owner p) k : ℝ) ≤
      ∑ᶠ k ∈ {k : ℤ | 0 < w.2 ((polygonalInputOf w).owner p) k},
        ((w.2 ((polygonalInputOf w).owner p) k : ℝ) + ((w.2 ((polygonalInputOf w).owner p) k : ℝ))⁻¹) := by
    rw [tsum_eq_sum hvan, finsum_mem_eq_finite_toFinset_sum _ hS]
    exact Finset.sum_le_sum fun k _ => le_add_of_nonneg_right (inv_nonneg.2 (Nat.cast_nonneg _))
  have hratio := cell_ratio_unitCell_le h hi h0p
  unfold rootDensity CellConfig.area
  rw [pi_toGMS_cellNC h, hI.coe_cellNC]
  exact (mul_le_mul_of_nonneg_left hpi (div_nonneg (sq_nonneg _) ENNReal.toReal_nonneg)).trans hratio

/-- **`π* ≤ π` in the polygonal configuration of a valid datum**: its conductances are integers. -/
theorem piStar_polygonalConfig_le_pi (h : UnitMeshValid w) (K : Cell) :
    (polygonalConfig H₀ w).1.piStar K ≤ (polygonalConfig H₀ w).1.pi K := by
  have hnat : ∀ n : ℕ, (n : ℝ) = 0 ∨ 1 ≤ (n : ℝ) := fun n => by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · left
      rw [h0, Nat.cast_zero]
    · right
      exact Nat.one_le_cast.mpr h0
  rw [polygonalConfig_of_valid h]
  refine LatticeProb.CellConfigWalk.piStar_le_pi_of_one_le _ K fun K' => ?_
  change (polygonalInputOf w).cellConfig.c K K' = 0 ∨ 1 ≤ (polygonalInputOf w).cellConfig.c K K'
  rw [PolygonalInput.cellConfig_c_eq]
  split_ifs
  · exact hnat _
  · exact Or.inl rfl

end MatedCRT.ZeroConePolygonal
