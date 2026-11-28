import MatedCRT.FirstPass.Derived.ZeroConePolygonalCells

/-!
# The GMS cell configuration of the polygonal cells

A valid `PolygonalInput` gives the polygonal cells `C_j` (`PolygonalInput.cell`). This file packages
them as a Gwynne-Miller-Sheffield cell configuration (`ReflectedGMS.GMS.CellConfig`) on the same
weighted graph.

* `PolygonalInput.cellNC j`: the cell `C_j` as an element of `NonemptyCompacts Plane`.
* `PolygonalInput.cellConfig`: the cells are the range of `cellNC`, the conductance of `cellNC a` and
  `cellNC b` is `m a b`, and it is `0` off the range.
* `PolygonalInput.isCellConfiguration`, `PolygonalInput.toGMS`: for a valid input this is a cell
  configuration, a point of the GMS space.
* `PolygonalInput.exists_equiv_cells`: the labels are in bijection with the cells, the conductances
  are the counts `m`, the vertex `v_j` lies in the `j`-th cell, and every point of an old cell `K_j`
  lies in a cell within its diameter of a point of the `j`-th cell.
* `PolygonalInput.lineConnected`, `PolygonalInput.connected_horizontal`,
  `PolygonalInput.connected_vertical`: connectedness along lines (answer, line 27), from connectedness
  at points (`IsValid.reflTransGen_point`) and the closed cover argument for compact connected sets.
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology Relation

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open ReflectedGMS ReflectedGMS.GMS

namespace PolygonalInput

variable (I : PolygonalInput)

open Classical in
/-- **The polygonal cell `C_j` as a nonempty compact set** (junk value `{0}` if `C_j` is not nonempty
and compact, which does not happen for a valid input). -/
def cellNC (j : ℤ) : Cell :=
  if h : IsCompact (I.cell j) ∧ (I.cell j).Nonempty then ⟨⟨I.cell j, h.1⟩, h.2⟩
  else ⟨⟨{0}, isCompact_singleton⟩, singleton_nonempty _⟩

open Classical in
/-- **The GMS cell configuration of the polygonal cells**: the cells are `C_j`, `j ∈ ℤ`, and the
conductance of `C_a` and `C_b` is `m a b` (`0` off the range). -/
def cellConfig : CellConfig where
  cells := range I.cellNC
  c K K' :=
    if K ∈ range I.cellNC ∧ K' ∈ range I.cellNC then
      (I.m (Function.invFun I.cellNC K) (Function.invFun I.cellNC K') : ℝ)
    else 0

open Classical in
theorem cellConfig_c_eq (I : PolygonalInput) (K K' : Cell) :
    I.cellConfig.c K K' =
      if K ∈ range I.cellNC ∧ K' ∈ range I.cellNC then
        (I.m (Function.invFun I.cellNC K) (Function.invFun I.cellNC K') : ℝ)
      else 0 :=
  rfl

variable {I}

theorem IsValid.coe_cellNC (hI : I.IsValid) (j : ℤ) : (I.cellNC j : Set Plane) = I.cell j := by
  have h : IsCompact (I.cell j) ∧ (I.cell j).Nonempty :=
    ⟨hI.isCompact_cell j, ⟨I.v j, hI.v_mem_cell j⟩⟩
  simp [cellNC, h]

theorem IsValid.cellNC_injective (hI : I.IsValid) : Function.Injective I.cellNC := fun i j h =>
  hI.cell_injective (by rw [← hI.coe_cellNC i, ← hI.coe_cellNC j, h])

theorem IsValid.cellConfig_c (hI : I.IsValid) (a b : ℤ) :
    I.cellConfig.c (I.cellNC a) (I.cellNC b) = (I.m a b : ℝ) := by
  have h : I.cellNC a ∈ range I.cellNC ∧ I.cellNC b ∈ range I.cellNC := ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
  rw [cellConfig_c_eq, if_pos h, Function.leftInverse_invFun hI.cellNC_injective a,
    Function.leftInverse_invFun hI.cellNC_injective b]

theorem cellConfig_c_of_not_mem {K K' : Cell} (h : ¬ (K ∈ range I.cellNC ∧ K' ∈ range I.cellNC)) :
    I.cellConfig.c K K' = 0 := by
  rw [cellConfig_c_eq, if_neg h]

/-- A positive conductance comes from two labels. -/
theorem IsValid.exists_of_adj (hI : I.IsValid) {K K' : Cell} (h : 0 < I.cellConfig.c K K') :
    ∃ a b, K = I.cellNC a ∧ K' = I.cellNC b ∧ 0 < I.m a b := by
  by_cases hmem : K ∈ range I.cellNC ∧ K' ∈ range I.cellNC
  · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hmem
    rw [hI.cellConfig_c] at h
    exact ⟨a, b, rfl, rfl, by exact_mod_cast h⟩
  · rw [cellConfig_c_of_not_mem hmem] at h
    exact absurd h (lt_irrefl _)

/-- **The polygonal cells form a cell configuration** (GMS Definition 1.15). -/
theorem isCellConfiguration (I : PolygonalInput) (hI : I.IsValid) :
    I.cellConfig.IsCellConfiguration where
  locallyFinite z := by
    refine ⟨ball z 1, ball_mem_nhds z one_pos, ?_⟩
    refine ((hI.finite_cells_meeting z 1).image I.cellNC).subset ?_
    rintro K ⟨⟨j, rfl⟩, y, hy, hyU⟩
    rw [hI.coe_cellNC] at hy
    exact ⟨j, ⟨y, hy, ball_subset_closedBall hyU⟩, rfl⟩
  isConnected := by
    rintro K ⟨j, rfl⟩
    rw [hI.coe_cellNC]
    exact hI.isConnected_cell j
  interior_nonempty := by
    rintro K ⟨j, rfl⟩
    rw [hI.coe_cellNC]
    exact hI.interior_cell_nonempty j
  iUnion_eq_univ := by
    refine eq_univ_of_forall fun z => ?_
    obtain ⟨j, hj⟩ := hI.exists_mem_cell z
    exact mem_iUnion₂.2 ⟨I.cellNC j, ⟨j, rfl⟩, by rw [hI.coe_cellNC]; exact hj⟩
  volume_inter := by
    rintro K ⟨i, rfl⟩ K' ⟨j, rfl⟩ hne
    rw [hI.coe_cellNC, hI.coe_cellNC]
    exact hI.volume_cell_inter fun h => hne (h ▸ rfl)
  c_nonneg K K' := by
    rw [cellConfig_c_eq]
    split_ifs
    · exact Nat.cast_nonneg _
    · exact le_rfl
  c_symm K K' := by
    rw [cellConfig_c_eq, cellConfig_c_eq]
    by_cases h : K ∈ range I.cellNC ∧ K' ∈ range I.cellNC
    · rw [if_pos h, if_pos ⟨h.2, h.1⟩, hI.m_symm]
    · rw [if_neg h, if_neg fun h' => h ⟨h'.2, h'.1⟩]
  adj_mem K K' h := by
    obtain ⟨a, b, rfl, rfl, -⟩ := hI.exists_of_adj h
    exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
  adj_ne K K' h := by
    obtain ⟨a, b, rfl, rfl, hab⟩ := hI.exists_of_adj h
    rintro heq
    have := hI.cellNC_injective heq
    subst this
    rw [hI.m_diag] at hab
    exact lt_irrefl _ hab
  adj_inter K K' h := by
    obtain ⟨a, b, rfl, rfl, hab⟩ := hI.exists_of_adj h
    rw [hI.coe_cellNC, hI.coe_cellNC]
    exact hI.cell_inter_nonempty hab

/-- **The GMS configuration of the polygonal cells** as a point of the GMS space. -/
def toGMS (I : PolygonalInput) (hI : I.IsValid) : GMSSpace :=
  ⟨I.cellConfig, I.isCellConfiguration hI⟩

/-- **The labels are the cells**: the labels `ℤ` are in bijection with the cells of `cellConfig`, the
conductances are the counts `m`, the vertex `v_j` lies in the `j`-th cell, and every point `z` of an old
cell `K_j` lies in some cell `K'` that has a point of the `j`-th cell within its diameter of `z`. -/
theorem exists_equiv_cells (I : PolygonalInput) (hI : I.IsValid) :
    ∃ e : ℤ ≃ I.cellConfig.cells, (∀ a b, I.cellConfig.c (e a) (e b) = I.m a b) ∧
      (∀ j, I.v j ∈ (e j : Set Plane)) ∧
      ∀ j, ∀ z ∈ I.K j, ∃ K' : I.cellConfig.cells, z ∈ (K' : Set Plane) ∧
        ∃ y ∈ (e j : Set Plane), dist z y ≤ Metric.diam (K' : Set Plane) := by
  refine ⟨Equiv.ofInjective I.cellNC hI.cellNC_injective, fun a b => hI.cellConfig_c a b,
    fun j => ?_, fun j z hz => ?_⟩
  · change I.v j ∈ (I.cellNC j : Set Plane)
    rw [hI.coe_cellNC]
    exact hI.v_mem_cell j
  · obtain ⟨k, hzk, y, hyj, hd⟩ := hI.exists_near hz
    refine ⟨Equiv.ofInjective I.cellNC hI.cellNC_injective k, ?_, y, ?_, ?_⟩
    · change z ∈ (I.cellNC k : Set Plane)
      rwa [hI.coe_cellNC]
    · change y ∈ (I.cellNC j : Set Plane)
      rwa [hI.coe_cellNC]
    · change dist z y ≤ Metric.diam (I.cellNC k : Set Plane)
      rwa [hI.coe_cellNC]

/-- **Connectedness at a point**: the polygonal cells through `z` induce a connected graph. -/
theorem inducedGraph_singleton_connected (I : PolygonalInput) (hI : I.IsValid) (z : Plane) :
    (I.cellConfig.inducedGraph {z}).Connected := by
  have hmem : ∀ j, z ∈ I.cell j → ((I.cellNC j : Set Plane) ∩ {z}).Nonempty := fun j hj =>
    ⟨z, by rw [hI.coe_cellNC]; exact hj, rfl⟩
  let mk : ∀ j, z ∈ I.cell j → {K : I.cellConfig.cells | ((K : Set Plane) ∩ {z}).Nonempty} :=
    fun j hj => ⟨⟨I.cellNC j, ⟨j, rfl⟩⟩, hmem j hj⟩
  have hreach : ∀ i j (hi : z ∈ I.cell i),
      ReflTransGen (fun a b => 0 < I.m a b ∧ z ∈ I.cell a ∧ z ∈ I.cell b) i j →
        ∃ hj : z ∈ I.cell j, (I.cellConfig.inducedGraph {z}).Reachable (mk i hi) (mk j hj) := by
    intro i j hi h
    induction h with
    | refl => exact ⟨hi, SimpleGraph.Reachable.refl _⟩
    | @tail b c _ hbc ih =>
      obtain ⟨hb, hr⟩ := ih
      have hne : b ≠ c := fun h => by
        subst h
        have := hbc.1
        rw [hI.m_diag] at this
        exact lt_irrefl _ this
      refine ⟨hbc.2.2, hr.trans (SimpleGraph.Adj.reachable ?_)⟩
      refine ⟨fun h => hne (hI.cellNC_injective ?_), ?_, ?_⟩
      · exact congrArg (fun x : I.cellConfig.cells => (x : Cell)) h
      · change 0 < I.cellConfig.c (I.cellNC b) (I.cellNC c)
        rw [hI.cellConfig_c]
        exact_mod_cast hbc.1
      · change 0 < I.cellConfig.c (I.cellNC c) (I.cellNC b)
        rw [hI.cellConfig_c, hI.m_symm]
        exact_mod_cast hbc.1
  refine (SimpleGraph.connected_iff _).2 ⟨fun u w => ?_, ?_⟩
  · obtain ⟨⟨K, ⟨i, rfl⟩⟩, hu⟩ := u
    obtain ⟨⟨K', ⟨j, rfl⟩⟩, hw⟩ := w
    have hi : z ∈ I.cell i := by
      obtain ⟨y, hy, hyz⟩ := hu
      rw [← hI.coe_cellNC]
      rwa [← (show y = z from hyz)]
    have hj : z ∈ I.cell j := by
      obtain ⟨y, hy, hyz⟩ := hw
      rw [← hI.coe_cellNC]
      rwa [← (show y = z from hyz)]
    exact (hreach i j hi (hI.reflTransGen_point z hi hj)).2
  · obtain ⟨j, hj⟩ := hI.exists_mem_cell z
    exact ⟨mk j hj⟩

/-- **The polygonal cell configuration is connected along lines.** -/
theorem lineConnected (I : PolygonalInput) (hI : I.IsValid) : I.cellConfig.LineConnected :=
  (CellConfig.lineConnected_iff_forall_singleton (I.isCellConfiguration hI)).2
    (I.inducedGraph_singleton_connected hI)

/-- **Connectedness along horizontal segments** (answer, line 27). -/
theorem connected_horizontal (I : PolygonalInput) (hI : I.IsValid) {a b : ℝ} (hab : a < b)
    (y : ℝ) : (I.cellConfig.inducedGraph (horizontal a b y)).Connected :=
  (I.lineConnected hI).1 a b y hab

/-- **Connectedness along vertical segments** (answer, line 27). -/
theorem connected_vertical (I : PolygonalInput) (hI : I.IsValid) (x : ℝ) {a b : ℝ}
    (hab : a < b) : (I.cellConfig.inducedGraph (vertical x a b)).Connected :=
  (I.lineConnected hI).2 x a b hab

end PolygonalInput

end MatedCRT.ZeroConePolygonal
