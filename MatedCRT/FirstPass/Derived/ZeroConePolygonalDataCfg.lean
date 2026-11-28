import MatedCRT.FirstPass.Derived.ZeroConePolygonalData

/-!
# Valid unit-mesh data from a line-connected cell configuration

A cell configuration `H` of the GMS space which is connected along lines and whose cells are
labelled by `ℤ` with the cells `K_j = η([j - 1, j])` of a unit-mesh datum `w = (η, m)` and the
conductances `m` gives a `UnitMeshValid w`:

* `UnitMeshValid.of_cellConfig`: positive area (nonempty interior), local finiteness, coverage,
  null overlaps and meeting of adjacent cells are the corresponding properties of a cell
  configuration; the symmetry and zero diagonal of `m` are those of the conductance, and the
  point connectivity of the labels (the field `pt`) is connectedness along lines at a single
  point, read through the labelling.
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology Relation

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open ReflectedGMS ReflectedGMS.GMS

variable {w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)}

/-- **A line-connected labelled cell configuration gives a valid unit-mesh datum.** -/
theorem UnitMeshValid.of_cellConfig (H : CellConfig) (hH : H.IsCellConfiguration)
    (hL : H.LineConnected) (e : ℤ ≃ H.cells)
    (hcell : ∀ a, ((e a : Cell) : Set Plane) = unitCell w a)
    (hc : ∀ a b, H.c (e a) (e b) = (w.2 a b : ℝ)) : UnitMeshValid w where
  volume_pos j := by
    obtain ⟨x, hx⟩ := hH.interior_nonempty (e j) (e j).2
    rw [hcell] at hx
    exact lt_of_lt_of_le (isOpen_interior.measure_pos volume ⟨x, hx⟩)
      (measure_mono interior_subset)
  lf A hA := by
    have hfin := CellConfig.finite_restrict_of_isCompact hH hA
    refine (hfin.preimage (f := fun j : ℤ => ((e j : H.cells) : Cell))
      (Subtype.val_injective.comp e.injective).injOn).subset ?_
    intro j hj
    obtain ⟨x, hx, hxA⟩ := hj
    rw [← hcell] at hx
    exact ⟨(e j).2, x, hx, hxA⟩
  cover z := by
    have hz : z ∈ ⋃ K ∈ H.cells, (K : Set Plane) := by
      rw [hH.iUnion_eq_univ]
      exact mem_univ z
    obtain ⟨K, hK, hzK⟩ := mem_iUnion₂.1 hz
    refine ⟨e.symm ⟨K, hK⟩, ?_⟩
    rw [← hcell, Equiv.apply_symm_apply]
    exact hzK
  volume_inter i j hij := by
    have := hH.volume_inter (e i) (e i).2 (e j) (e j).2
      (fun h => hij (e.injective (Subtype.ext h)))
    rwa [hcell, hcell] at this
  m_symm i j := by
    have h1 := hH.c_symm (e i) (e j)
    rw [hc, hc] at h1
    exact_mod_cast h1
  m_diag j := by
    by_contra hne
    have hpos : 0 < H.c (e j) (e j) := by
      rw [hc]
      exact_mod_cast Nat.pos_of_ne_zero hne
    exact hH.adj_ne _ _ hpos rfl
  m_inter i j hij := by
    have hpos : H.Adj (e i) (e j) := by
      change 0 < H.c (e i) (e j)
      rw [hc]
      exact_mod_cast hij
    have := hH.adj_inter _ _ hpos
    rwa [hcell, hcell] at this
  pt z i j hi hj := by
    have hpt := ((CellConfig.lineConnected_iff_forall_singleton hH).1 hL z).preconnected
    have hmem : ∀ a, z ∈ unitCell w a →
        ((((e a : H.cells) : Cell) : Set Plane) ∩ {z}).Nonempty := fun a ha =>
      Set.inter_singleton_nonempty.2 (by rw [hcell]; exact ha)
    have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).1
      (hpt ⟨e i, hmem i hi⟩ ⟨e j, hmem j hj⟩)
    have key := ReflTransGen.lift
      (fun x : {K : H.cells | ((K : Set Plane) ∩ {z}).Nonempty} => e.symm x.1)
      (p := fun a b => 0 < w.2 a b ∧ z ∈ unitCell w a ∧ z ∈ unitCell w b)
      (fun x y hxy => by
        have hx := Set.inter_singleton_nonempty.1 x.2
        have hy := Set.inter_singleton_nonempty.1 y.2
        have hxy' := hc (e.symm x.1) (e.symm y.1)
        simp only [Equiv.apply_symm_apply] at hxy'
        refine ⟨?_, ?_, ?_⟩
        · have := hxy.2.1
          change 0 < H.c x.1 y.1 at this
          rw [hxy'] at this
          exact_mod_cast this
        · rw [← hcell, Equiv.apply_symm_apply]
          exact hx
        · rw [← hcell, Equiv.apply_symm_apply]
          exact hy) _ _ hr
    simpa only [Function.onFun, Equiv.symm_apply_apply] using key

end MatedCRT.ZeroConePolygonal
