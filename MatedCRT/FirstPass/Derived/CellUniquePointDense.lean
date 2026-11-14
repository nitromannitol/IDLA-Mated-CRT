import MatedCRT.FirstPass.S5c.HExclusive

/-!
# Points lying in a single cell are dense in each cell

For an area parametrization `η` of `μ` (`IsAreaParametrized μ η`: `η` is continuous and `μ(η([a, b])) = b - a` for
`a < b`) and `ε > 0`, every relative neighbourhood of a point `y` of the cell `H^ε_k = η([ε(k - 1), εk])` contains a
point of `H^ε_k` lying in no other cell `H^ε_j`, `j ≠ k`.

Proof: continuity of `η` gives a nondegenerate parameter interval `[a', b'] ⊆ [ε(k - 1), εk]` whose image lies in the
ball `B_r(y)`; by the area parametrization this image has `μ`-mass `b' - a' > 0`, while the points of `H^ε_k` lying in
another cell form a `μ`-null set, since distinct cells meet in a `μ`-null set (`MatedCRT.S5c.cell_inter_null_of_lt`).
Only the continuity of `η` and the area formula are used: no local finiteness of `μ`, nor `η(0) = 0`, nor surjectivity.

The almost sure forms are for the curve `S.η` of a valid environment and for a continuous version `η'` of it (the
curve of the interpolated walk law `interpWalkLaw S η'`).

## Main results

* `MatedCRT.exists_dist_lt_mem_cell_notMem_cell_of_ne`: the deterministic statement.
* `MatedCRT.ae_exists_dist_lt_mem_cell_notMem_cell_of_ne`: almost surely for `S.η`, all `ε > 0` at once.
* `MatedCRT.ae_exists_dist_lt_mem_cell_notMem_cell_of_ne_of_ae_eq`: the same for a version `η'` of `S.η`.
-/

namespace MatedCRT

open MeasureTheory Set Metric

/-- For an area parametrization, the points of the cell `H^ε_k` lying in another cell form a `μ`-null set. -/
theorem measure_cell_inter_iUnion_ne_null {μ : Measure ℂ} {η : ℝ → ℂ} (hap : IsAreaParametrized μ η) {ε : ℝ}
    (hε : 0 < ε) (k : ℤ) : μ (⋃ j : ℤ, ⋃ (_ : j ≠ k), cell ε η k ∩ cell ε η j) = 0 := by
  refine measure_iUnion_null fun j => measure_iUnion_null fun hj => ?_
  rcases lt_trichotomy j k with h | h | h
  · rw [inter_comm]
    exact S5c.cell_inter_null_of_lt hap hε h
  · exact absurd h hj
  · exact S5c.cell_inter_null_of_lt hap hε h

/-- **Points lying in a single cell are dense in each cell.** For an area parametrization `η` of `μ` and `ε > 0`, for
every point `y` of the cell `H^ε_k = η([ε(k - 1), εk])` and every `r > 0` there is a point `z'` of `H^ε_k` with
`|y - z'| < r` lying in no other cell `H^ε_j`, `j ≠ k`. -/
theorem exists_dist_lt_mem_cell_notMem_cell_of_ne {μ : Measure ℂ} {η : ℝ → ℂ} (hap : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) {k : ℤ} {y : ℂ} (hy : y ∈ cell ε η k) {r : ℝ} (hr : 0 < r) :
    ∃ z', dist y z' < r ∧ z' ∈ cell ε η k ∧ ∀ j ≠ k, z' ∉ cell ε η j := by
  have hy' : y ∈ η '' Icc (ε * ((k : ℝ) - 1)) (ε * (k : ℝ)) := hy
  obtain ⟨t, ht, rfl⟩ := hy'
  have hpq : ε * ((k : ℝ) - 1) < ε * (k : ℝ) := mul_lt_mul_of_pos_left (by linarith) hε
  obtain ⟨δ, hδ, hδη⟩ := Metric.continuous_iff.mp hap.1 t r hr
  -- a nondegenerate parameter interval inside the cell interval and the `δ / 2`-neighbourhood of `t`
  have hab : max (ε * ((k : ℝ) - 1)) (t - δ / 2) < min (ε * (k : ℝ)) (t + δ / 2) := by
    refine max_lt (lt_min hpq ?_) (lt_min ?_ ?_)
    · linarith [ht.1]
    · linarith [ht.2]
    · linarith
  have hsub : η '' Icc (max (ε * ((k : ℝ) - 1)) (t - δ / 2)) (min (ε * (k : ℝ)) (t + δ / 2)) ⊆ cell ε η k :=
    image_mono (Icc_subset_Icc (le_max_left _ _) (min_le_left _ _))
  have hpos : 0 < μ (η '' Icc (max (ε * ((k : ℝ) - 1)) (t - δ / 2)) (min (ε * (k : ℝ)) (t + δ / 2))) := by
    rw [hap.2.2.2 _ _ hab]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  have hnot : ¬ (η '' Icc (max (ε * ((k : ℝ) - 1)) (t - δ / 2)) (min (ε * (k : ℝ)) (t + δ / 2)) ⊆
      ⋃ j : ℤ, ⋃ (_ : j ≠ k), cell ε η k ∩ cell ε η j) := fun hcov =>
    hpos.ne' (measure_mono_null hcov (measure_cell_inter_iUnion_ne_null hap hε k))
  obtain ⟨z, hz, hzN⟩ := not_subset.mp hnot
  have hzk : z ∈ cell ε η k := hsub hz
  obtain ⟨s, hs, rfl⟩ := hz
  refine ⟨η s, ?_, hzk, fun j hj hzj => hzN (mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hj, hzk, hzj⟩⟩)⟩
  have h1 : s ≤ t + δ / 2 := hs.2.trans (min_le_right _ _)
  have h2 : t - δ / 2 ≤ s := (le_max_right _ _).trans hs.1
  rw [dist_comm]
  refine hδη s ?_
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

/-- Almost surely, for the curve `S.η` of a valid environment, points lying in a single cell are dense in each cell,
for all cell sizes `ε > 0` simultaneously. -/
theorem ae_exists_dist_lt_mem_cell_notMem_cell_of_ne {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ ε > 0, ∀ (k : ℤ) (y : ℂ), y ∈ cell ε (S.η ω) k → ∀ r > 0,
      ∃ z', dist y z' < r ∧ z' ∈ cell ε (S.η ω) k ∧ ∀ j ≠ k, z' ∉ cell ε (S.η ω) j := by
  filter_upwards [hS.isAreaParametrized] with ω hω
  intro ε hε k y hy r hr
  exact exists_dist_lt_mem_cell_notMem_cell_of_ne hω hε hy hr

/-- Almost surely, for a continuous version `η'` of the curve `S.η` of a valid environment, points lying in a single
cell of `η'` are dense in each cell, for all cell sizes `ε > 0` simultaneously. -/
theorem ae_exists_dist_lt_mem_cell_notMem_cell_of_ne_of_ae_eq {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (η' : Ω → C(ℝ, ℂ))
    (hη' : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) :
    ∀ᵐ ω ∂S.P, ∀ ε > 0, ∀ (k : ℤ) (y : ℂ), y ∈ cell ε (⇑(η' ω)) k → ∀ r > 0,
      ∃ z', dist y z' < r ∧ z' ∈ cell ε (⇑(η' ω)) k ∧ ∀ j ≠ k, z' ∉ cell ε (⇑(η' ω)) j := by
  filter_upwards [ae_exists_dist_lt_mem_cell_notMem_cell_of_ne hS, hη'] with ω hω hωη
  rw [hωη]
  exact hω

end MatedCRT
