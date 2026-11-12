import MatedCRT.FirstPass.Derived.BlockCells
import MatedCRT.FirstPass.Derived.CountingMeasureOfCellSize

/-!
# Blocks of consecutive cells (preliminaries for BG20 Lemma A.5)

In the proof of BG20 Lemma A.5 the cells of `G^ε` are grouped into blocks of `N` consecutive cells, which are the
cells of `G^{Nε}` (`FirstPass.Derived.cell_mul_eq_iUnion`). This file collects the elementary facts used there:

* `blockIndex N k = ⌊(k - 1)/N⌋ + 1`, the index of the block containing the cell `k`: `mem_Ioc_blockIndex`,
  `eq_of_mem_Ioc_mul` (the blocks are disjoint), `blockIndex_eq_of_mem_Ioc`, `cell_subset_cell_blockIndex`;
* `cell_nonempty`: cells are nonempty;
* `mem_ball_of_not_mem_thickening_sphere`: a point of `B_r` at distance at least `a` from `∂B_r` has its whole
  `a`-neighbourhood inside `B_r`;
* `polyHighProb_comp_of_le_rpow`: an event holding with polynomially high probability as `δ → 0` still does when
  `δ = φ(ε)` with `0 < φ(ε) ≤ ε^k` (used with `φ(ε) = ⌊ε^{-1/2}⌋ ε`).
-/

open Set Metric MeasureTheory Filter Topology HarmonicBalls

namespace MatedCRT

/-- The index of the block of `N` consecutive cells containing the cell `k`: `k ∈ (N(j - 1), Nj]`. -/
def blockIndex (N : ℕ) (k : ℤ) : ℤ := (k - 1) / N + 1

theorem mem_Ioc_blockIndex {N : ℕ} (hN : 0 < N) (k : ℤ) :
    k ∈ Finset.Ioc ((N : ℤ) * (blockIndex N k - 1)) ((N : ℤ) * blockIndex N k) := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have h1 := Int.mul_ediv_add_emod (k - 1) N
  have h2 := Int.emod_nonneg (k - 1) hN'.ne'
  have h3 := Int.add_one_le_of_lt (Int.emod_lt_of_pos (k - 1) hN')
  rw [Finset.mem_Ioc, blockIndex, add_sub_cancel_right, mul_add, mul_one]
  constructor <;> linarith

/-- The blocks `(N(j - 1), Nj]` are pairwise disjoint. -/
theorem eq_of_mem_Ioc_mul {N : ℕ} (hN : 0 < N) {k j j' : ℤ}
    (h : k ∈ Finset.Ioc ((N : ℤ) * (j - 1)) ((N : ℤ) * j))
    (h' : k ∈ Finset.Ioc ((N : ℤ) * (j' - 1)) ((N : ℤ) * j')) : j = j' := by
  rw [Finset.mem_Ioc] at h h'
  have hN' : (0 : ℤ) ≤ N := by positivity
  have a1 : j - 1 < j' := lt_of_mul_lt_mul_left (h.1.trans_le h'.2) hN'
  have a2 : j' - 1 < j := lt_of_mul_lt_mul_left (h'.1.trans_le h.2) hN'
  omega

theorem blockIndex_eq_of_mem_Ioc {N : ℕ} (hN : 0 < N) {k j : ℤ}
    (h : k ∈ Finset.Ioc ((N : ℤ) * (j - 1)) ((N : ℤ) * j)) : blockIndex N k = j :=
  eq_of_mem_Ioc_mul hN (mem_Ioc_blockIndex hN k) h

/-- The cell `H^ε_k` lies in the block cell `H^{Nε}_{blockIndex N k}`. -/
theorem cell_subset_cell_blockIndex (η : ℝ → ℂ) {ε : ℝ} {N : ℕ} (hN : 0 < N) (k : ℤ) :
    cell ε η k ⊆ cell ((N : ℝ) * ε) η (blockIndex N k) := by
  rw [FirstPass.Derived.cell_mul_eq_iUnion η hN]
  intro x hx
  simp only [mem_iUnion]
  exact ⟨k, mem_Ioc_blockIndex hN k, hx⟩

theorem cell_nonempty (η : ℝ → ℂ) {ε : ℝ} (hε : 0 ≤ ε) (k : ℤ) : (cell ε η k).Nonempty :=
  (nonempty_Icc.2 (mul_le_mul_of_nonneg_left (by linarith) hε)).image η

/-- If `x ∈ B_r` is at distance at least `a` from the circle `∂B_r`, then every `y` with `|y - x| < a` lies in
`B_r`. -/
theorem mem_ball_of_not_mem_thickening_sphere {r a : ℝ} {x y : ℂ} (hx : x ∈ ball (0 : ℂ) r)
    (hxa : x ∉ thickening a (sphere (0 : ℂ) r)) (hxy : ‖y - x‖ < a) : y ∈ ball (0 : ℂ) r := by
  rw [mem_ball_zero_iff] at hx ⊢
  by_contra hy
  rw [not_lt] at hy
  have hcont : ContinuousOn (fun t : ℝ => ‖x + (t : ℂ) * (y - x)‖) (Icc 0 1) := by fun_prop
  obtain ⟨t, ht, htr⟩ := intermediate_value_Icc zero_le_one hcont
    ⟨by simpa using hx.le, by simpa using hy⟩
  apply hxa
  rw [mem_thickening_iff]
  refine ⟨x + (t : ℂ) * (y - x), by simpa [mem_sphere_zero_iff_norm] using htr, ?_⟩
  have hd : dist x (x + (t : ℂ) * (y - x)) = t * ‖y - x‖ := by
    rw [dist_eq_norm]
    simp [abs_of_nonneg ht.1]
  rw [hd]
  calc t * ‖y - x‖ ≤ 1 * ‖y - x‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
    _ < a := by rwa [one_mul]

/-- **Change of scale for polynomially high probability.** If `E δ` holds with polynomially high probability as
`δ → 0` and `0 < φ(ε) ≤ ε^k` for small `ε`, with `k > 0`, then `E (φ ε)` holds with polynomially high probability as
`ε → 0`. -/
theorem polyHighProb_comp_of_le_rpow {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : ℝ → Set Ω}
    (hE : PolyHighProb P E) {k : ℝ} (hk : 0 < k) {φ : ℝ → ℝ}
    (hφ : ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → 0 < φ ε ∧ φ ε ≤ ε ^ k) :
    PolyHighProb P fun ε => E (φ ε) := by
  obtain ⟨p, hp, C, r₀, hr₀, hb⟩ := hE
  obtain ⟨ε₀, hε₀, hφ⟩ := hφ
  refine ⟨k * p, mul_pos hk hp, max C 0, min ε₀ (r₀ ^ (1 / k)),
    lt_min hε₀ (Real.rpow_pos_of_pos hr₀ _), fun ε hε hεr => ?_⟩
  obtain ⟨hφ0, hφk⟩ := hφ ε hε (lt_of_lt_of_le hεr (min_le_left _ _))
  have h2 : ε < r₀ ^ (1 / k) := lt_of_lt_of_le hεr (min_le_right _ _)
  have h3 : ε ^ k < r₀ := by
    calc ε ^ k < (r₀ ^ (1 / k)) ^ k := Real.rpow_lt_rpow hε.le h2 hk
      _ = r₀ := by rw [← Real.rpow_mul hr₀.le, one_div_mul_cancel hk.ne', Real.rpow_one]
  refine (hb (φ ε) hφ0 (lt_of_le_of_lt hφk h3)).trans (ENNReal.ofReal_le_ofReal ?_)
  calc C * φ ε ^ p ≤ max C 0 * φ ε ^ p :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hφ0.le _)
    _ ≤ max C 0 * (ε ^ k) ^ p :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hφ0.le hφk hp.le) (le_max_right _ _)
    _ = max C 0 * ε ^ (k * p) := by rw [← Real.rpow_mul hε.le]

end MatedCRT
