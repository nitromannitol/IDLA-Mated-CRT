import MatedCRT.FirstPass.Derived.BlockDegreeRunningMin

/-!
# Running-minimum cells of a block as unit-interval running-minimum hits

Berestycki–Gwynne (2020), Appendix A, proof of Lemma A.9: the cells of a block `[a + 1, a + N]` of
cells of size `ε` containing a running minimum of a path `X`, relative to the start `ε a` of the
block, correspond to the unit intervals `[j - 1, j]`, `1 ≤ j ≤ N`, containing a running minimum
(relative to time `0`) of the recentred, rescaled path `u ↦ X (ε a + ε u)` on `ℝ≥0`. Any
transformation of the values that preserves their order (for instance `x ↦ c (x - d)` with
`c > 0`, the Brownian rescaling) leaves the count unchanged. The same holds for the time reversal of
`X` on the block, with the path `u ↦ X (ε (a + N) - ε u)`.

## Main results

* `card_blockRunningMinCells_eq_card_filter`: the count of running-minimum cells of the block equals
  the count of unit intervals `[j - 1, j]`, `1 ≤ j ≤ N`, containing a running-minimum time of any
  path `Y : ℝ≥0 → ℝ` with the order of `u ↦ X (ε a + ε u)`;
* `card_blockRunningMinCells_blockReversal_eq_card_filter`: the same for the time reversal on the
  block and the path `u ↦ X (ε (a + N) - ε u)`;
* `card_blockRunningMinCells_eq_card_filter_affine`,
  `card_blockRunningMinCells_blockReversal_eq_card_filter_affine`: the affine images
  `u ↦ c (X (ε a + ε u) - d)` and `u ↦ c (X (ε (a + N) - ε u) - d)`, `c > 0`.
-/

open Finset

open scoped NNReal

namespace MatedCRT

/-- A cell `a + j` of the block `[a + 1, a + N]` contains a running minimum of `X` relative to `ε a`
exactly when the unit interval `[j - 1, j]` contains a running minimum, relative to `0`, of a path
`Y` on `ℝ≥0` with the order of `u ↦ X (ε a + ε u)`. -/
theorem blockRunningMinCell_iff {ε : ℝ} (hε : 0 < ε) {X : ℝ → ℝ} {Y : ℝ≥0 → ℝ} (a : ℤ)
    (hY : ∀ u v : ℝ≥0, Y u ≤ Y v ↔ X (ε * a + ε * u) ≤ X (ε * a + ε * v)) {j : ℕ} (hj : 1 ≤ j) :
    (∃ t ∈ Set.Icc (ε * ((a + j : ℤ) : ℝ) - ε) (ε * ((a + j : ℤ) : ℝ)),
      ∀ s ∈ Set.Icc (ε * ((a + 1 : ℤ) : ℝ) - ε) t, X t ≤ X s) ↔
      ∃ t : ℝ≥0, ((j - 1 : ℕ) : ℝ≥0) ≤ t ∧ t ≤ j ∧ ∀ s ≤ t, Y t ≤ Y s := by
  have hj1 : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by rw [Nat.cast_sub hj, Nat.cast_one]
  have hlo : ε * ((a + 1 : ℤ) : ℝ) - ε = ε * a := by push_cast; ring
  have hk : ε * ((a + j : ℤ) : ℝ) = ε * a + ε * j := by push_cast; ring
  rw [hlo, hk]
  constructor
  · rintro ⟨t, ⟨ht1, ht2⟩, hmin⟩
    have hta : ε * a ≤ t := by
      have := mul_le_mul_of_nonneg_left ((Nat.one_le_cast (α := ℝ)).2 hj) hε.le
      linarith
    have hu0 : 0 ≤ (t - ε * a) / ε := div_nonneg (sub_nonneg.2 hta) hε.le
    set u : ℝ≥0 := Real.toNNReal ((t - ε * a) / ε) with hu_def
    have hu : (u : ℝ) = (t - ε * a) / ε := by rw [hu_def, Real.coe_toNNReal', max_eq_left hu0]
    have hεu : ε * a + ε * (u : ℝ) = t := by rw [hu]; field_simp; ring
    refine ⟨u, ?_, ?_, fun s hs => ?_⟩
    · apply NNReal.coe_le_coe.1
      rw [NNReal.coe_natCast, hj1, hu, le_div_iff₀ hε]
      linarith
    · apply NNReal.coe_le_coe.1
      rw [NNReal.coe_natCast, hu, div_le_iff₀ hε]
      linarith
    · apply (hY u s).2
      rw [hεu]
      have hs' : (s : ℝ) ≤ u := NNReal.coe_le_coe.2 hs
      rw [hu, le_div_iff₀ hε] at hs'
      have hs0 : 0 ≤ ε * (s : ℝ) := mul_nonneg hε.le s.2
      exact hmin _ ⟨by linarith, by linarith⟩
  · rintro ⟨u, hu1, hu2, hmin⟩
    have hu1' : (j : ℝ) - 1 ≤ u := by
      have h := NNReal.coe_le_coe.2 hu1
      rwa [NNReal.coe_natCast, hj1] at h
    have hu2' : (u : ℝ) ≤ j := by
      have h := NNReal.coe_le_coe.2 hu2
      rwa [NNReal.coe_natCast] at h
    have h1 := mul_le_mul_of_nonneg_left hu1' hε.le
    have h2 := mul_le_mul_of_nonneg_left hu2' hε.le
    refine ⟨ε * a + ε * u, ⟨by linarith, by linarith⟩, fun s hs => ?_⟩
    obtain ⟨hs1, hs2⟩ := hs
    have hv0 : 0 ≤ (s - ε * a) / ε := div_nonneg (sub_nonneg.2 hs1) hε.le
    set v : ℝ≥0 := Real.toNNReal ((s - ε * a) / ε) with hv_def
    have hv : (v : ℝ) = (s - ε * a) / ε := by rw [hv_def, Real.coe_toNNReal', max_eq_left hv0]
    have hεv : ε * a + ε * (v : ℝ) = s := by rw [hv]; field_simp; ring
    have hvu : v ≤ u := by
      apply NNReal.coe_le_coe.1
      rw [hv, div_le_iff₀ hε]
      linarith
    have h := (hY u v).1 (hmin v hvu)
    rwa [hεv] at h

open Classical in
/-- The running-minimum cells of the block `[a + 1, a + N]` correspond to the unit intervals
`[j - 1, j]`, `1 ≤ j ≤ N`, containing a running-minimum time of a path `Y` on `ℝ≥0` with the order
of `u ↦ X (ε a + ε u)` (BG20, proof of Lemma A.9). -/
theorem card_blockRunningMinCells_eq_card_filter {ε : ℝ} (hε : 0 < ε) (X : ℝ → ℝ) (Y : ℝ≥0 → ℝ)
    (a : ℤ) (N : ℕ) (hY : ∀ u v : ℝ≥0, Y u ≤ Y v ↔ X (ε * a + ε * u) ≤ X (ε * a + ε * v)) :
    #(blockRunningMinCells ε X (a + 1) (a + N)) =
      #((Icc 1 N).filter fun j => ∃ t : ℝ≥0, ((j - 1 : ℕ) : ℝ≥0) ≤ t ∧ t ≤ j ∧ ∀ s ≤ t, Y t ≤ Y s) := by
  symm
  refine card_nbij' (fun j => a + (j : ℤ)) (fun k => (k - a).toNat) ?_ ?_ ?_ ?_
  · intro j hj
    dsimp only
    rw [mem_coe, mem_filter, mem_Icc] at hj
    obtain ⟨⟨hj1, hjN⟩, hhit⟩ := hj
    rw [mem_coe, mem_blockRunningMinCells, mem_Icc]
    exact ⟨⟨by omega, by omega⟩, (blockRunningMinCell_iff hε a hY hj1).2 hhit⟩
  · intro k hk
    dsimp only
    rw [mem_coe, mem_blockRunningMinCells, mem_Icc] at hk
    obtain ⟨⟨hk1, hkN⟩, hcell⟩ := hk
    have hj1 : 1 ≤ (k - a).toNat := by omega
    have hkj : k = a + ((k - a).toNat : ℤ) := by omega
    rw [mem_coe, mem_filter, mem_Icc]
    refine ⟨⟨hj1, by omega⟩, (blockRunningMinCell_iff hε a hY hj1).1 ?_⟩
    rw [← hkj]
    exact hcell
  · intro j _
    dsimp only
    omega
  · intro k hk
    rw [mem_coe, mem_blockRunningMinCells, mem_Icc] at hk
    dsimp only
    omega

open Classical in
/-- The running-minimum cells of the time reversal of `X` on the block `[a + 1, a + N]` correspond
to the unit intervals `[j - 1, j]`, `1 ≤ j ≤ N`, containing a running-minimum time of a path `Y` on
`ℝ≥0` with the order of `u ↦ X (ε (a + N) - ε u)`. -/
theorem card_blockRunningMinCells_blockReversal_eq_card_filter {ε : ℝ} (hε : 0 < ε) (X : ℝ → ℝ)
    (Y : ℝ≥0 → ℝ) (a : ℤ) (N : ℕ)
    (hY : ∀ u v : ℝ≥0, Y u ≤ Y v ↔
      X (ε * ((a + N : ℤ) : ℝ) - ε * u) ≤ X (ε * ((a + N : ℤ) : ℝ) - ε * v)) :
    #(blockRunningMinCells ε (blockReversal ε X (a + 1) (a + N)) (a + 1) (a + N)) =
      #((Icc 1 N).filter fun j => ∃ t : ℝ≥0, ((j - 1 : ℕ) : ℝ≥0) ≤ t ∧ t ≤ j ∧ ∀ s ≤ t, Y t ≤ Y s) := by
  refine card_blockRunningMinCells_eq_card_filter hε _ Y a N fun u v => ?_
  have h : ∀ w : ℝ, blockReversal ε X (a + 1) (a + N) (ε * a + ε * w) =
      X (ε * ((a + N : ℤ) : ℝ) - ε * w) := by
    intro w
    simp only [blockReversal]
    congr 1
    push_cast
    ring
  rw [h, h]
  exact hY u v

open Classical in
/-- The affine image `u ↦ c (X (ε a + ε u) - d)`, `c > 0`, of the block path has the same
running-minimum count. -/
theorem card_blockRunningMinCells_eq_card_filter_affine {ε : ℝ} (hε : 0 < ε) (X : ℝ → ℝ) (a : ℤ)
    (N : ℕ) {c : ℝ} (hc : 0 < c) (d : ℝ) :
    #(blockRunningMinCells ε X (a + 1) (a + N)) =
      #((Icc 1 N).filter fun j => ∃ t : ℝ≥0, ((j - 1 : ℕ) : ℝ≥0) ≤ t ∧ t ≤ j ∧
        ∀ s ≤ t, c * (X (ε * a + ε * t) - d) ≤ c * (X (ε * a + ε * s) - d)) :=
  card_blockRunningMinCells_eq_card_filter hε X _ a N fun u v => by
    rw [mul_le_mul_iff_right₀ hc, sub_le_sub_iff_right]

open Classical in
/-- The affine image `u ↦ c (X (ε (a + N) - ε u) - d)`, `c > 0`, of the reversed block path has the
same running-minimum count as the time reversal of `X` on the block. -/
theorem card_blockRunningMinCells_blockReversal_eq_card_filter_affine {ε : ℝ} (hε : 0 < ε)
    (X : ℝ → ℝ) (a : ℤ) (N : ℕ) {c : ℝ} (hc : 0 < c) (d : ℝ) :
    #(blockRunningMinCells ε (blockReversal ε X (a + 1) (a + N)) (a + 1) (a + N)) =
      #((Icc 1 N).filter fun j => ∃ t : ℝ≥0, ((j - 1 : ℕ) : ℝ≥0) ≤ t ∧ t ≤ j ∧
        ∀ s ≤ t, c * (X (ε * ((a + N : ℤ) : ℝ) - ε * t) - d) ≤
          c * (X (ε * ((a + N : ℤ) : ℝ) - ε * s) - d)) :=
  card_blockRunningMinCells_blockReversal_eq_card_filter hε X _ a N fun u v => by
    rw [mul_le_mul_iff_right₀ hc, sub_le_sub_iff_right]

end MatedCRT
