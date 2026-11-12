import MatedCRT.FirstPass.Derived.BlockRunningMinTail
import MatedCRT.FirstPass.Derived.BlockCells
import MatedCRT.FirstPass.Derived.CountingMeasureOfCellSize

/-!
# The block degree estimate on the good event

Berestycki–Gwynne (2020), proof of Lemma A.5, (A.43): deterministic consequences of the events entering the
block degree estimate. Blocks are the cells of size `δ = Nε`; the `ε`-cells of the block `j` are the cells
`k ∈ (N(j - 1), Nj]`.

## Main results

* `cell_subset_ball_of_diam_le`: a cell of diameter at most `s` meeting `B_ρ` lies in `B_{ρ + s}`;
* `mem_cellVertices_of_mem_Ioc_mul`: the `ε`-cells of a block contained in `D` are vertices of `V^ε(D)`;
* `blockIndexRange`, `card_blockIndexRange_le`: a deterministic range of at most `2M/δ + 2` block indices
  containing every block of an area-parametrized curve which lies in `η([-M, M])`
  (`IsAreaParametrized.mem_blockIndexRange_of_diam_le`);
* `MatedCRTEnv.abs_sum_matedDeg_block_sub_le_of_runningMin_le`: on the event where the multiplicities are
  locally finite, the cell minima of `L` and `R` are distinct, the degrees in `B_{ρ'}` are at most `D` and the
  running-minimum count of the block is at most `4m`, every block of diameter at most `s` meeting `B_ρ`,
  `ρ + s ≤ ρ'`, has degree sum within `2 + 4 (2 + D) m` of `6N`.
-/

open Finset MeasureTheory Metric

namespace MatedCRT

/-- A cell of diameter at most `s` meeting `B_ρ` lies in `B_{ρ'}` whenever `ρ + s ≤ ρ'`. -/
theorem cell_subset_ball_of_diam_le {η : ℝ → ℂ} (hη : Continuous η) {δ ρ ρ' s : ℝ} {j : ℤ}
    (hj : (cell δ η j ∩ ball 0 ρ).Nonempty) (hdiam : diam (cell δ η j) ≤ s) (hs : ρ + s ≤ ρ') :
    cell δ η j ⊆ ball 0 ρ' := by
  obtain ⟨y, hyc, hyB⟩ := hj
  intro x hx
  rw [mem_ball_zero_iff] at hyB ⊢
  have hxy : dist x y ≤ s :=
    (dist_le_diam_of_mem (isCompact_cell hη δ j).isBounded hx hyc).trans hdiam
  rw [dist_eq_norm] at hxy
  calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
    _ < ρ' := by linarith

/-- The `ε`-cells `k ∈ (N(j - 1), Nj]` of the block `j` are contained in the cell `j` of size `Nε`; if the latter
lies in `D`, they are vertices of `V^ε(D)`. -/
theorem mem_cellVertices_of_mem_Ioc_mul {η : ℝ → ℂ} {ε : ℝ} (hε : 0 ≤ ε) {N : ℕ} (hN : 0 < N)
    {j k : ℤ} (hk : k ∈ Finset.Ioc ((N : ℤ) * (j - 1)) ((N : ℤ) * j)) {D : Set ℂ}
    (hD : cell ((N : ℝ) * ε) η j ⊆ D) : k ∈ cellVertices ε η D := by
  have hsub : cell ε η k ⊆ cell ((N : ℝ) * ε) η j := by
    rw [FirstPass.Derived.cell_mul_eq_iUnion η hN j]
    intro x hx
    exact Set.mem_iUnion₂.2 ⟨k, hk, hx⟩
  have hle : ε * ((k : ℝ) - 1) ≤ ε * k := mul_le_mul_of_nonneg_left (by linarith) hε
  exact ⟨η (ε * k), ⟨ε * k, ⟨hle, le_rfl⟩, rfl⟩, hD (hsub ⟨ε * k, ⟨hle, le_rfl⟩, rfl⟩)⟩

/-- A deterministic range of block indices: it contains every `j` with `-M < δ j` and `δ (j - 1) < M`
(`mem_blockIndexRange`) and has at most `2M/δ + 2` elements (`card_blockIndexRange_le`). -/
noncomputable def blockIndexRange (δ M : ℝ) : Finset ℤ :=
  Finset.Ioo ⌊-M / δ⌋ (⌈M / δ⌉ + 1)

theorem mem_blockIndexRange {δ M : ℝ} (hδ : 0 < δ) {j : ℤ} (h1 : -M < δ * j)
    (h2 : δ * (j - 1) < M) : j ∈ blockIndexRange δ M := by
  rw [blockIndexRange, Finset.mem_Ioo]
  constructor
  · have h : -M / δ < j := by
      rw [div_lt_iff₀ hδ]
      linarith
    exact Int.floor_lt.2 h
  · have h : (j : ℝ) - 1 < M / δ := by
      rw [lt_div_iff₀ hδ]
      linarith
    have h' : (j : ℝ) - 1 < ⌈M / δ⌉ := h.trans_le (Int.le_ceil _)
    have h'' : j - 1 < ⌈M / δ⌉ := by exact_mod_cast h'
    omega

theorem card_blockIndexRange_le {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) :
    ((blockIndexRange δ M).card : ℝ) ≤ 2 * M / δ + 2 := by
  rw [blockIndexRange, Int.card_Ioo]
  have hMδ : 0 ≤ M / δ := div_nonneg hM hδ.le
  have h1 : (⌈M / δ⌉ : ℝ) < M / δ + 1 := Int.ceil_lt_add_one _
  have h2 : -M / δ - 1 < (⌊-M / δ⌋ : ℝ) := Int.sub_one_lt_floor _
  have hfc : (⌊-M / δ⌋ : ℝ) ≤ ⌈M / δ⌉ := by
    have : -M / δ ≤ M / δ := by
      rw [neg_div]
      linarith
    exact (Int.floor_le _).trans (this.trans (Int.le_ceil _))
  have hfc' : ⌊-M / δ⌋ ≤ ⌈M / δ⌉ := by exact_mod_cast hfc
  have hnn : 0 ≤ ⌈M / δ⌉ + 1 - ⌊-M / δ⌋ - 1 := by omega
  have hcast : (((⌈M / δ⌉ + 1 - ⌊-M / δ⌋ - 1).toNat : ℕ) : ℝ) =
      ((⌈M / δ⌉ + 1 - ⌊-M / δ⌋ - 1 : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
  rw [hcast]
  push_cast
  have h4 : -M / δ = -(M / δ) := neg_div _ _
  have h3 : 2 * M / δ = M / δ + M / δ := by ring
  linarith

/-- For an area-parametrized curve with `B_1 ⊆ η([-M, M])`, every block of size `δ` of diameter at most `s`
meeting `B_ρ`, `ρ + s ≤ 1`, has its index in `blockIndexRange δ M`. -/
theorem IsAreaParametrized.mem_blockIndexRange_of_diam_le {μ : Measure ℂ} {η : ℝ → ℂ}
    (hpar : IsAreaParametrized μ η) (hη : Continuous η) {δ M ρ s : ℝ} (hδ : 0 < δ) (hM : 0 < M)
    (hcov : ball (0 : ℂ) 1 ⊆ η '' Set.Icc (-M) M) (hs : ρ + s ≤ 1) {j : ℤ}
    (hj : (cell δ η j ∩ ball 0 ρ).Nonempty) (hdiam : diam (cell δ η j) ≤ s) :
    j ∈ blockIndexRange δ M := by
  obtain ⟨h1, h2⟩ :=
    hpar.cell_index_bounds hδ hM ((cell_subset_ball_of_diam_le hη hj hdiam hs).trans hcov)
  exact mem_blockIndexRange hδ h1 h2

/-- **The degree sum of a block on the good event** (BG20 (A.43)). If the edge multiplicities are locally
finite, the cell minima of `L` and of `R` are distinct, every vertex of `V^ε(B_{ρ'})` has degree at most `D`,
and the running-minimum count of the block `j` is at most `4m`, then a block of diameter at most `s` meeting
`B_ρ`, with `ρ + s ≤ ρ'`, has degree sum within `2 + (2 + D) 4m` of `6N`. -/
theorem MatedCRTEnv.abs_sum_matedDeg_block_sub_le_of_runningMin_le {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : 1 ≤ N) {ω : Ω}
    (hη : Continuous (S.η ω)) (hlf : IsLocallyFiniteMult (S.mult ε ω))
    (hinjL : Function.Injective (bmCellMin ε fun t => (S.bm ω t).1))
    (hinjR : Function.Injective (bmCellMin ε fun t => (S.bm ω t).2))
    {ρ ρ' s D m : ℝ} (hs : ρ + s ≤ ρ') (hD0 : 0 ≤ D)
    (hdeg : ∀ k ∈ cellVertices ε (S.η ω) (ball 0 ρ'), (matedDeg (S.mult ε ω) k : ℝ) ≤ D)
    {j : ℤ} (hj : (cell ((N : ℝ) * ε) (S.η ω) j ∩ ball 0 ρ).Nonempty)
    (hdiam : diam (cell ((N : ℝ) * ε) (S.η ω) j) ≤ s)
    (hK : (blockRunningMinCount ε (fun t => (S.bm ω t).1) (fun t => (S.bm ω t).2)
      ((N : ℤ) * (j - 1) + 1) ((N : ℤ) * (j - 1) + N) : ℝ) ≤ 4 * m) :
    |∑ k ∈ Finset.Ioc ((N : ℤ) * (j - 1)) ((N : ℤ) * j), (matedDeg (S.mult ε ω) k : ℝ) - 6 * N| ≤
      2 + (2 + D) * (4 * m) := by
  have hN0 : 0 < N := hN
  have hsub := cell_subset_ball_of_diam_le hη hj hdiam hs
  have hjN : (N : ℤ) * j = (N : ℤ) * (j - 1) + N := by ring
  have hD : ∀ k ∈ Finset.Icc ((N : ℤ) * (j - 1) + 1) ((N : ℤ) * (j - 1) + N),
      (matedDeg (S.mult ε ω) k : ℝ) ≤ D := by
    intro k hk
    refine hdeg k (mem_cellVertices_of_mem_Ioc_mul hε.le hN0 ?_ hsub)
    rw [Finset.mem_Icc] at hk
    rw [hjN, Finset.mem_Ioc]
    omega
  have hblk := S.abs_sum_matedDeg_block_sub_le_runningMin hε hlf ((N : ℤ) * (j - 1)) hN
    hinjL.injOn hinjR.injOn hD
  rw [hjN]
  have h2D : 0 ≤ 2 + D := by linarith
  have := mul_le_mul_of_nonneg_left hK h2D
  linarith

end MatedCRT
