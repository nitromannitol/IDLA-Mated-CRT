import MatedCRT.Defs.Setting
import MatedCRT.Defs.Map

/-!
# FIRST PASS, 5.3 (MeanValueSurplusLowerStep): exclusive representatives of the cells

For an area parametrization `η` of `μ`, the cells
`H^ε_a = η([ε(a-1), εa])` of distinct labels meet in a `μ`-null set (their masses add up to the mass of the union), so every
cell `H^ε_a` (of positive mass `ε`) contains a point `x` lying in no other cell. For such `x`, `vertexOf ε η x = a`.
This avoids the false shortcut `vertexOf ε η (vertexPoint ε η a) = a` (the representative can lie in an earlier cell).
The point `x` is chosen inside a deterministic proof: no measurable choice is needed.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- Two adjacent pieces of the image of `[u, w]`, split at `s`, meet in a null set. -/
theorem measure_image_inter_null {μ : Measure ℂ} {η : ℝ → ℂ} (hap : IsAreaParametrized μ η) {u s w : ℝ}
    (hus : u < s) (hsw : s < w) :
    μ (η '' Icc u s ∩ η '' Icc s w) = 0 := by
  have hmeas : MeasurableSet (η '' Icc s w) := (isCompact_Icc.image hap.1).isClosed.measurableSet
  have hU : η '' Icc u s ∪ η '' Icc s w = η '' Icc u w := by
    rw [← image_union, Icc_union_Icc_eq_Icc hus.le hsw.le]
  have hA := hap.2.2.2 u s hus
  have hB := hap.2.2.2 s w hsw
  have hC := hap.2.2.2 u w (hus.trans hsw)
  have key : μ (η '' Icc u s ∪ η '' Icc s w) + μ (η '' Icc u s ∩ η '' Icc s w) =
      μ (η '' Icc u s) + μ (η '' Icc s w) := measure_union_add_inter (η '' Icc u s) hmeas
  rw [hU, hC, hA, hB, ← ENNReal.ofReal_add (sub_nonneg.mpr hus.le) (sub_nonneg.mpr hsw.le)] at key
  have hsum : s - u + (w - s) = w - u := by ring
  rw [hsum] at key
  have h0 : ENNReal.ofReal (w - u) + μ (η '' Icc u s ∩ η '' Icc s w) = ENNReal.ofReal (w - u) + 0 := by
    rw [add_zero]
    exact key
  exact (ENNReal.add_right_inj ENNReal.ofReal_ne_top).mp h0

/-- Distinct cells of an area parametrization meet in a `μ`-null set (the labels `a < b`, `ε > 0`). -/
theorem cell_inter_null_of_lt {μ : Measure ℂ} {η : ℝ → ℂ} (hap : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε)
    {a b : ℤ} (hab : a < b) : μ (cell ε η a ∩ cell ε η b) = 0 := by
  have hab' : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
  have hab'' : (a : ℝ) < b := by exact_mod_cast hab
  have hsub : cell ε η a ∩ cell ε η b ⊆
      η '' Icc (ε * ((a : ℝ) - 1)) (ε * ((b : ℝ) - 1)) ∩ η '' Icc (ε * ((b : ℝ) - 1)) (ε * (b : ℝ)) := by
    apply inter_subset_inter
    · exact image_mono (Icc_subset_Icc le_rfl (mul_le_mul_of_nonneg_left (by linarith) hε.le))
    · exact subset_rfl
  exact measure_mono_null hsub
    (measure_image_inter_null hap (mul_lt_mul_of_pos_left (by linarith) hε)
      (mul_lt_mul_of_pos_left (by linarith) hε))

/-- Every cell of positive area parameter has positive mass `ε`. -/
theorem cell_measure_pos {μ : Measure ℂ} {η : ℝ → ℂ} (hap : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε)
    (a : ℤ) : 0 < μ (cell ε η a) := by
  have hlt : ε * ((a : ℝ) - 1) < ε * (a : ℝ) := mul_lt_mul_of_pos_left (by linarith) hε
  have h := hap.2.2.2 _ _ hlt
  have hval : ε * (a : ℝ) - ε * ((a : ℝ) - 1) = ε := by ring
  rw [hval] at h
  show 0 < μ (η '' Icc (ε * ((a : ℝ) - 1)) (ε * (a : ℝ)))
  rw [h]
  exact ENNReal.ofReal_pos.mpr hε

/-- **Exclusive representative**: every cell `H^ε_a` contains a point lying in no
other cell. -/
theorem exists_exclusive_mem_cell {μ : Measure ℂ} {η : ℝ → ℂ} (hap : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε)
    (a : ℤ) : ∃ x ∈ cell ε η a, ∀ b : ℤ, x ∈ cell ε η b → b = a := by
  have hBad0 : μ (⋃ b : ℤ, ⋃ (_ : b ≠ a), cell ε η a ∩ cell ε η b) = 0 := by
    refine measure_iUnion_null fun b => measure_iUnion_null fun hb => ?_
    rcases lt_or_gt_of_ne hb with h | h
    · rw [inter_comm]
      exact cell_inter_null_of_lt hap hε h
    · exact cell_inter_null_of_lt hap hε h
  have hnot : ¬ (cell ε η a ⊆ ⋃ b : ℤ, ⋃ (_ : b ≠ a), cell ε η a ∩ cell ε η b) := fun hsub =>
    (cell_measure_pos hap hε a).ne' (measure_mono_null hsub hBad0)
  obtain ⟨x, hxa, hxB⟩ := not_subset.mp hnot
  refine ⟨x, hxa, fun b hxb => ?_⟩
  by_contra hne
  exact hxB (mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨hne, ⟨hxa, hxb⟩⟩⟩)

/-- For an exclusive point of the cell of `a`, the smallest-label vertex is `a`. -/
theorem vertexOf_eq_of_exclusive {ε : ℝ} {η : ℝ → ℂ} {x : ℂ} {a : ℤ} (hxa : x ∈ cell ε η a)
    (hex : ∀ b : ℤ, x ∈ cell ε η b → b = a) : vertexOf ε η x = a := by
  have hset : {k : ℤ | x ∈ cell ε η k} = {a} := by
    ext k
    constructor
    · intro hk
      exact mem_singleton_iff.mpr (hex k hk)
    · intro hk
      rw [mem_singleton_iff.mp hk]
      exact hxa
  show sInf {k : ℤ | x ∈ cell ε η k} = a
  rw [hset, csInf_singleton]

end MatedCRT.S5c
