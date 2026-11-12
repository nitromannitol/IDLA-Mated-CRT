import MatedCRT.FirstPass.Derived.DegreeCountingBlocks
import MatedCRT.FirstPass.Derived.DegreeWeightedMeasureCells

/-!
# Degree-weighted counting bounds by blocks of cells (deterministic core of BG20 Lemma A.5)

In the proof of BG20 Lemma A.5 the cells of `G^ε` are grouped into blocks of `N` consecutive cells, the
cells `H^{δ}_j` of `G^{δ}`, `δ = Nε`. If every block cell meeting `B_ρ` has diameter at most `s` and
degree sum `∑_{k ∈ (N(j-1), Nj]} deg^ε(k)` within `E` of `6N`, then the degree-weighted counting sum
`∑_{k ∈ V^ε(B_r)} deg^ε(k) g(w_k)` is compared with the counting sum of the blocks, and the deterministic
counting bound of BG20 Lemma A.4 (`IsAreaParametrized.counting_bounds`) at the scale `δ` gives

`6 ε⁻¹ ∫_{B_r \ B_a(∂B_r)} g dμ - Err ≤ ∑_{k ∈ V^ε(B_r)} deg^ε(k) g(w_k) ≤ 6 ε⁻¹ ∫_{B_a(B_r)} g dμ + Err`

with `Err = (2M/δ + 5) (L E + L s (12 N + E))` (`IsAreaParametrized.degree_counting_bounds`).

* `IsAreaParametrized.exists_finset_cellVertices`: `V^ε(D)` is finite with at most `2M/ε + 5` elements;
* `exists_cellPoints`: points `u_j ∈ H^ε_j ∩ cl(D)` for `j ∈ V^ε(D)`;
* `IsAreaParametrized.degree_counting_upper`, `IsAreaParametrized.degree_counting_lower`: the two halves
  as finite sums.
-/

open Set Metric MeasureTheory Filter Topology HarmonicBalls

namespace MatedCRT

variable {μ : Measure ℂ} {η : ℝ → ℂ}

/-- If every cell meeting `B_ρ` has diameter at most `s < a`, `ρ + a ≤ 1` and `B_1 ⊆ η([-M, M])`, then for
`D ⊆ B_ρ` the vertex set `V^ε(D)` is finite with at most `2M/ε + 5` elements. -/
theorem IsAreaParametrized.exists_finset_cellVertices (hpar : IsAreaParametrized μ η)
    {ε M ρ a s : ℝ} (hε : 0 < ε) (hM : 0 < M) (hsa : s < a) (hρa : ρ + a ≤ 1)
    (hcov : ball (0 : ℂ) 1 ⊆ η '' Icc (-M) M)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball 0 ρ).Nonempty → diam (cell ε η k) ≤ s)
    {D : Set ℂ} (hD : D ⊆ ball 0 ρ) :
    ∃ F : Finset ℤ, (∀ k, k ∈ F ↔ k ∈ cellVertices ε η D) ∧ (F.card : ℝ) ≤ 2 * M / ε + 5 := by
  classical
  set V := cellVertices ε η D with hV
  have hcell1 : ∀ k ∈ V, cell ε η k ⊆ ball 0 1 := by
    rintro k ⟨y, hyc, hyD⟩ x hx
    have hyρ := mem_ball_zero_iff.1 (hD hyD)
    have hd := (dist_le_diam_of_mem (isCompact_cell hpar.1 ε k).isBounded hx hyc).trans
      (hdiam k ⟨y, hyc, hD hyD⟩)
    rw [dist_eq_norm] at hd
    have h1 := norm_sub_norm_le x y
    rw [mem_ball_zero_iff]
    linarith
  set n : ℕ := ⌈M / ε⌉₊ + 1 with hn
  have hVn : ∀ k ∈ V, k ∈ Finset.Icc (-(n : ℤ)) n := by
    intro k hk
    have hb := hpar.cell_index_bounds hε hM ((hcell1 k hk).trans hcov)
    have hc := Nat.le_ceil (M / ε)
    have h1 : -(M / ε) < k := by
      rw [neg_div', div_lt_iff₀ hε]
      linarith
    have h2 : (k : ℝ) - 1 < M / ε := by
      rw [lt_div_iff₀ hε]
      linarith
    have h3 : -((n : ℤ) : ℝ) < k := by push_cast [hn]; linarith
    have h4 : (k : ℝ) < (n : ℤ) + 1 := by push_cast [hn]; linarith
    rw [Finset.mem_Icc]
    constructor
    · exact_mod_cast h3.le
    · have : k < (n : ℤ) + 1 := by exact_mod_cast h4
      omega
  have hfin : V.Finite := (Finset.Icc (-(n : ℤ)) n).finite_toSet.subset fun k hk => hVn k hk
  refine ⟨hfin.toFinset, fun k => hfin.mem_toFinset, ?_⟩
  have h1 : hfin.toFinset.card ≤ (Finset.Icc (-(n : ℤ)) n).card :=
    Finset.card_le_card fun k hk => hVn k (hfin.mem_toFinset.1 hk)
  rw [Int.card_Icc] at h1
  have h2 : ((n : ℤ) + 1 - -(n : ℤ)).toNat = 2 * n + 1 := by omega
  rw [h2] at h1
  have h3 : (n : ℝ) ≤ M / ε + 2 := by
    rw [hn]
    push_cast
    linarith [Nat.ceil_lt_add_one (div_nonneg hM.le hε.le)]
  have h4 : (hfin.toFinset.card : ℝ) ≤ 2 * n + 1 := by exact_mod_cast h1
  have h5 : 2 * (M / ε) = 2 * M / ε := by ring
  linarith

/-- Points `u_j ∈ H^ε_j ∩ cl(D)` for every vertex `j ∈ V^ε(D)`. -/
theorem exists_cellPoints (ε : ℝ) (η : ℝ → ℂ) (D : Set ℂ) :
    ∃ u : ℤ → ℂ, ∀ j ∈ cellVertices ε η D, u j ∈ cell ε η j ∩ closure D := by
  have h : ∀ j, ∃ u : ℂ, j ∈ cellVertices ε η D → u ∈ cell ε η j ∩ closure D := by
    intro j
    by_cases hj : j ∈ cellVertices ε η D
    · obtain ⟨y, hyc, hyD⟩ := hj
      exact ⟨y, fun _ => ⟨hyc, subset_closure hyD⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose u hu using h
  exact ⟨u, hu⟩

/-- Two points of a cell of diameter at most `s` are within distance `s`. -/
theorem norm_sub_le_of_mem_cell (hη : Continuous η) {δ ρ s : ℝ} {j : ℤ}
    (hdiam : (cell δ η j ∩ ball 0 ρ).Nonempty → diam (cell δ η j) ≤ s)
    (hj : (cell δ η j ∩ ball 0 ρ).Nonempty) {x y : ℂ} (hx : x ∈ cell δ η j) (hy : y ∈ cell δ η j) :
    ‖x - y‖ ≤ s := by
  rw [← dist_eq_norm]
  exact (dist_le_diam_of_mem (isCompact_cell hη δ j).isBounded hx hy).trans (hdiam hj)

/-- The blocks `(N(j - 1), Nj]` are pairwise disjoint. -/
theorem pairwiseDisjoint_Ioc_mul {N : ℕ} (hN : 0 < N) (F : Finset ℤ) :
    (F : Set ℤ).PairwiseDisjoint fun j => Finset.Ioc ((N : ℤ) * (j - 1)) ((N : ℤ) * j) :=
  fun _ _ _ _ hjj' => Finset.disjoint_left.2 fun _ hk hk' => hjj' (eq_of_mem_Ioc_mul hN hk hk')

/-- **Upper half of the deterministic core of BG20 Lemma A.5.** The block cells of scale `δ = Nε` meeting
`B_ρ` have diameter at most `s` and degree sum within `E` of `6N`; `g` is nonnegative, bounded by `L` and
`L`-Lipschitz; `w_k ∈ H^ε_k`. Then the degree-weighted counting sum over the finite set `t = V^ε(B_r)` is at
most `6 ε⁻¹ ∫_{B_a(B_r)} g dμ + (2M/δ + 5)(L E + L s (12 N + E))`. -/
theorem IsAreaParametrized.degree_counting_upper (hpar : IsAreaParametrized μ η) {m : ℤ → ℤ → ℕ}
    {ε M ρ a s L E : ℝ} {N : ℕ} (hε : 0 < ε) (hN : 0 < N) (hM : 0 < M) (hs : 0 ≤ s) (hsa : s < a)
    (hρa : ρ + a ≤ 1) (hL : 0 ≤ L) (hE : 0 ≤ E) (hcov : ball (0 : ℂ) 1 ⊆ η '' Icc (-M) M)
    (hdiam : ∀ j : ℤ, (cell (N * ε) η j ∩ ball 0 ρ).Nonempty → diam (cell (N * ε) η j) ≤ s)
    (hdeg : ∀ j : ℤ, (cell (N * ε) η j ∩ ball 0 ρ).Nonempty →
      |(∑ k ∈ Finset.Ioc ((N : ℤ) * (j - 1)) ((N : ℤ) * j), (matedDeg m k : ℝ)) - 6 * N| ≤ E)
    {r : ℝ} (hrρ : r ≤ ρ) {g : ℂ → ℝ} (hg : ∀ x, 0 ≤ g x ∧ |g x| ≤ L)
    (hgL : ∀ x y, |g x - g y| ≤ L * ‖x - y‖) {w : ℤ → ℂ}
    (hw : ∀ k ∈ cellVertices ε η (ball 0 r), w k ∈ cell ε η k) (t : Finset ℤ)
    (ht : ∀ k, k ∈ t ↔ k ∈ cellVertices ε η (ball 0 r)) :
    ∑ k ∈ t, (matedDeg m k : ℝ) * g (w k) ≤
      6 * ε⁻¹ * ∫ x in thickening a (ball 0 r), g x ∂μ +
        (2 * M / (N * ε) + 5) * (L * E + L * s * (12 * N + E)) := by
  classical
  set δ : ℝ := N * ε with hδ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ0 : 0 < δ := mul_pos hNr hε
  have hDρ : ball (0 : ℂ) r ⊆ ball 0 ρ := ball_subset_ball hrρ
  obtain ⟨F, hF, hFc⟩ := hpar.exists_finset_cellVertices hδ0 hM hsa hρa hcov hdiam hDρ
  obtain ⟨u, hu⟩ := exists_cellPoints δ η (ball (0 : ℂ) r)
  have hcnt := (hpar.counting_bounds hδ0 hM hs hsa hρa hL hcov hdiam hDρ
    (fun x _ => hg x) (fun x _ y _ => hgL x y) hu).2
  have hsumF : ∑' j : cellVertices δ η (ball (0 : ℂ) r), g (u j) = ∑ j ∈ F, g (u j) :=
    tsum_cellVertices_eq_sum F hF (fun j => g (u j))
  rw [hsumF] at hcnt
  have hjρ : ∀ j ∈ F, (cell δ η j ∩ ball 0 ρ).Nonempty := fun j hj => by
    obtain ⟨y, hyc, hyD⟩ := (hF j).1 hj
    exact ⟨y, hyc, hDρ hyD⟩
  -- every vertex of `V^ε(B_r)` lies in a block of `V^δ(B_r)`
  have hblk : ∀ k ∈ t, blockIndex N k ∈ F := by
    intro k hk
    obtain ⟨y, hyc, hyD⟩ := (ht k).1 hk
    exact (hF _).2 ⟨y, cell_subset_cell_blockIndex η hN k hyc, hyD⟩
  set B := F.biUnion fun j => Finset.Ioc ((N : ℤ) * (j - 1)) ((N : ℤ) * j) with hB
  have htB : t ⊆ B := by
    intro k hk
    rw [hB, Finset.mem_biUnion]
    exact ⟨_, hblk k hk, mem_Ioc_blockIndex hN k⟩
  have hterm : ∀ k ∈ t, (matedDeg m k : ℝ) * g (w k) ≤
      (matedDeg m k : ℝ) * (g (u (blockIndex N k)) + L * s) := by
    intro k hk
    have hjF := hblk k hk
    have hwk : w k ∈ cell δ η (blockIndex N k) :=
      cell_subset_cell_blockIndex η hN k (hw k ((ht k).1 hk))
    have hd := norm_sub_le_of_mem_cell hpar.1 (hdiam _) (hjρ _ hjF) hwk (hu _ ((hF _).1 hjF)).1
    have h1 := (abs_le.1 (hgL (w k) (u (blockIndex N k)))).2
    have h2 := mul_le_mul_of_nonneg_left hd hL
    exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  have hstep1 : ∑ k ∈ t, (matedDeg m k : ℝ) * g (w k) ≤
      ∑ k ∈ B, (matedDeg m k : ℝ) * (g (u (blockIndex N k)) + L * s) :=
    (Finset.sum_le_sum hterm).trans (Finset.sum_le_sum_of_subset_of_nonneg htB
      fun k _ _ => mul_nonneg (Nat.cast_nonneg _) (add_nonneg (hg _).1 (mul_nonneg hL hs)))
  have hstep2 : ∑ k ∈ B, (matedDeg m k : ℝ) * (g (u (blockIndex N k)) + L * s) ≤
      ∑ j ∈ F, (6 * N * g (u j) + (L * E + L * s * (6 * N + E))) := by
    rw [hB, Finset.sum_biUnion (pairwiseDisjoint_Ioc_mul hN F)]
    refine Finset.sum_le_sum fun j hj => ?_
    have hcongr : ∑ k ∈ Finset.Ioc ((N : ℤ) * (j - 1)) ((N : ℤ) * j),
        (matedDeg m k : ℝ) * (g (u (blockIndex N k)) + L * s) =
        (∑ k ∈ Finset.Ioc ((N : ℤ) * (j - 1)) ((N : ℤ) * j), (matedDeg m k : ℝ)) *
          (g (u j) + L * s) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k hk => by rw [blockIndex_eq_of_mem_Ioc hN hk]
    rw [hcongr]
    have hD := abs_le.1 (hdeg j (hjρ j hj))
    have hgj := hg (u j)
    have hgjL : g (u j) ≤ L := (le_abs_self _).trans hgj.2
    set S := ∑ k ∈ Finset.Ioc ((N : ℤ) * (j - 1)) ((N : ℤ) * j), (matedDeg m k : ℝ)
    have h1 : 0 ≤ (6 * N + E - S) * g (u j) := mul_nonneg (by linarith) hgj.1
    have h2 : 0 ≤ (6 * N + E - S) * (L * s) := mul_nonneg (by linarith) (mul_nonneg hL hs)
    have h3 : 0 ≤ E * (L - g (u j)) := mul_nonneg hE (by linarith)
    linarith
  have hstep3 : ∑ j ∈ F, (6 * N * g (u j) + (L * E + L * s * (6 * N + E))) =
      6 * N * ∑ j ∈ F, g (u j) + F.card * (L * E + L * s * (6 * N + E)) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  have hNδ : 6 * (N : ℝ) * δ⁻¹ = 6 * ε⁻¹ := by
    rw [hδ]
    field_simp
  have hc0 : 0 ≤ L * E + L * s * (6 * N + E) :=
    add_nonneg (mul_nonneg hL hE) (mul_nonneg (mul_nonneg hL hs) (by linarith))
  have hK := mul_le_mul_of_nonneg_right hFc hc0
  have hI := mul_le_mul_of_nonneg_left hcnt (by positivity : (0 : ℝ) ≤ 6 * N)
  have hI' : 6 * N * ∑ j ∈ F, g (u j) ≤ 6 * ε⁻¹ * ∫ x in thickening a (ball 0 r), g x ∂μ +
      6 * N * ((2 * M / δ + 5) * (L * s)) := by
    rw [← hNδ]
    linarith
  linarith

/-- **Lower half of the deterministic core of BG20 Lemma A.5.** Under the hypotheses of
`IsAreaParametrized.degree_counting_upper` and `0 < r`, the degree-weighted counting sum over
`t = V^ε(B_r)` is at least `6 ε⁻¹ ∫_{B_r \ B_a(∂B_r)} g dμ - (2M/δ + 5)(L E + L s (12 N + E))`: every block
cell meeting `B_r \ B_a(∂B_r)` lies in `B_r`, so all its cells belong to `V^ε(B_r)`. -/
theorem IsAreaParametrized.degree_counting_lower (hpar : IsAreaParametrized μ η) {m : ℤ → ℤ → ℕ}
    {ε M ρ a s L E : ℝ} {N : ℕ} (hε : 0 < ε) (hN : 0 < N) (hM : 0 < M) (hs : 0 ≤ s) (hsa : s < a)
    (hρa : ρ + a ≤ 1) (hL : 0 ≤ L) (hE : 0 ≤ E) (hcov : ball (0 : ℂ) 1 ⊆ η '' Icc (-M) M)
    (hdiam : ∀ j : ℤ, (cell (N * ε) η j ∩ ball 0 ρ).Nonempty → diam (cell (N * ε) η j) ≤ s)
    (hdeg : ∀ j : ℤ, (cell (N * ε) η j ∩ ball 0 ρ).Nonempty →
      |(∑ k ∈ Finset.Ioc ((N : ℤ) * (j - 1)) ((N : ℤ) * j), (matedDeg m k : ℝ)) - 6 * N| ≤ E)
    {r : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) {g : ℂ → ℝ} (hg : ∀ x, 0 ≤ g x ∧ |g x| ≤ L)
    (hgL : ∀ x y, |g x - g y| ≤ L * ‖x - y‖) {w : ℤ → ℂ}
    (hw : ∀ k ∈ cellVertices ε η (ball 0 r), w k ∈ cell ε η k) (t : Finset ℤ)
    (ht : ∀ k, k ∈ t ↔ k ∈ cellVertices ε η (ball 0 r)) :
    6 * ε⁻¹ * ∫ x in ball 0 r \ thickening a (frontier (ball 0 r)), g x ∂μ -
        (2 * M / (N * ε) + 5) * (L * E + L * s * (12 * N + E)) ≤
      ∑ k ∈ t, (matedDeg m k : ℝ) * g (w k) := by
  classical
  set δ : ℝ := N * ε with hδ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ0 : 0 < δ := mul_pos hNr hε
  set D' := ball (0 : ℂ) r \ thickening a (frontier (ball 0 r)) with hD'
  have hDρ : D' ⊆ ball 0 ρ := sdiff_subset.trans (ball_subset_ball hrρ)
  obtain ⟨F, hF, hFc⟩ := hpar.exists_finset_cellVertices hδ0 hM hsa hρa hcov hdiam hDρ
  obtain ⟨u, hu⟩ := exists_cellPoints δ η D'
  have hcnt := (hpar.counting_bounds hδ0 hM hs hsa hρa hL hcov hdiam hDρ
    (fun x _ => hg x) (fun x _ y _ => hgL x y) hu).1
  have hsumF : ∑' j : cellVertices δ η D', g (u j) = ∑ j ∈ F, g (u j) :=
    tsum_cellVertices_eq_sum F hF (fun j => g (u j))
  rw [hsumF] at hcnt
  have hjρ : ∀ j ∈ F, (cell δ η j ∩ ball 0 ρ).Nonempty := fun j hj => by
    obtain ⟨y, hyc, hyD⟩ := (hF j).1 hj
    exact ⟨y, hyc, hDρ hyD⟩
  have hfr : frontier (ball (0 : ℂ) r) = sphere 0 r := frontier_ball 0 hr.ne'
  -- block cells meeting `D'` lie in `B_r`
  have hHr : ∀ j ∈ F, cell δ η j ⊆ ball 0 r := by
    intro j hj x hx
    obtain ⟨y, hyc, hyD⟩ := (hF j).1 hj
    have hd := norm_sub_le_of_mem_cell hpar.1 (hdiam j) (hjρ j hj) hx hyc
    have hy2 : y ∉ thickening a (sphere 0 r) := by
      rw [← hfr]
      exact hyD.2
    exact mem_ball_of_not_mem_thickening_sphere hyD.1 hy2 (hd.trans_lt hsa)
  have hsubj : ∀ j ∈ F, ∀ k ∈ Finset.Ioc ((N : ℤ) * (j - 1)) ((N : ℤ) * j), cell ε η k ⊆ cell δ η j := by
    intro j _ k hkj
    have := cell_subset_cell_blockIndex η (ε := ε) hN k
    rwa [blockIndex_eq_of_mem_Ioc hN hkj] at this
  set B := F.biUnion fun j => Finset.Ioc ((N : ℤ) * (j - 1)) ((N : ℤ) * j) with hB
  have hBt : B ⊆ t := by
    intro k hk
    rw [hB, Finset.mem_biUnion] at hk
    obtain ⟨j, hj, hkj⟩ := hk
    rw [ht]
    obtain ⟨x, hx⟩ := cell_nonempty η hε.le k
    exact ⟨x, hx, hHr j hj (hsubj j hj k hkj hx)⟩
  have hstep1 : ∑ k ∈ B, (matedDeg m k : ℝ) * g (w k) ≤ ∑ k ∈ t, (matedDeg m k : ℝ) * g (w k) :=
    Finset.sum_le_sum_of_subset_of_nonneg hBt fun k _ _ => mul_nonneg (Nat.cast_nonneg _) (hg _).1
  have hstep2 : ∑ j ∈ F, (6 * N * g (u j) - (L * E + L * s * (6 * N + E))) ≤
      ∑ k ∈ B, (matedDeg m k : ℝ) * g (w k) := by
    rw [hB, Finset.sum_biUnion (pairwiseDisjoint_Ioc_mul hN F)]
    refine Finset.sum_le_sum fun j hj => ?_
    have hle : ∀ k ∈ Finset.Ioc ((N : ℤ) * (j - 1)) ((N : ℤ) * j),
        (matedDeg m k : ℝ) * (g (u j) - L * s) ≤ (matedDeg m k : ℝ) * g (w k) := by
      intro k hkj
      have hkt : k ∈ t := hBt (by rw [hB, Finset.mem_biUnion]; exact ⟨j, hj, hkj⟩)
      have hwk : w k ∈ cell δ η j := hsubj j hj k hkj (hw k ((ht k).1 hkt))
      have hd := norm_sub_le_of_mem_cell hpar.1 (hdiam j) (hjρ j hj) hwk (hu j ((hF j).1 hj)).1
      have h1 := (abs_le.1 (hgL (w k) (u j))).1
      have h2 := mul_le_mul_of_nonneg_left hd hL
      exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    refine le_trans ?_ (Finset.sum_le_sum hle)
    rw [← Finset.sum_mul]
    have hD := abs_le.1 (hdeg j (hjρ j hj))
    have hgj := hg (u j)
    have hgjL : g (u j) ≤ L := (le_abs_self _).trans hgj.2
    set S := ∑ k ∈ Finset.Ioc ((N : ℤ) * (j - 1)) ((N : ℤ) * j), (matedDeg m k : ℝ)
    have h1 : 0 ≤ (S - (6 * N - E)) * g (u j) := mul_nonneg (by linarith) hgj.1
    have h2 : 0 ≤ (6 * N + E - S) * (L * s) := mul_nonneg (by linarith) (mul_nonneg hL hs)
    have h3 : 0 ≤ E * (L - g (u j)) := mul_nonneg hE (by linarith)
    linarith
  have hstep3 : ∑ j ∈ F, (6 * N * g (u j) - (L * E + L * s * (6 * N + E))) =
      6 * N * ∑ j ∈ F, g (u j) - F.card * (L * E + L * s * (6 * N + E)) := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  have hNδ : 6 * (N : ℝ) * δ⁻¹ = 6 * ε⁻¹ := by
    rw [hδ]
    field_simp
  have hc0 : 0 ≤ L * E + L * s * (6 * N + E) :=
    add_nonneg (mul_nonneg hL hE) (mul_nonneg (mul_nonneg hL hs) (by linarith))
  have hK := mul_le_mul_of_nonneg_right hFc hc0
  have hI := mul_le_mul_of_nonneg_left hcnt (by positivity : (0 : ℝ) ≤ 6 * N)
  have hI' : 6 * ε⁻¹ * ∫ x in D', g x ∂μ - 6 * N * ((2 * M / δ + 5) * (L * s)) ≤
      6 * N * ∑ j ∈ F, g (u j) := by
    rw [← hNδ]
    linarith
  linarith

/-- **Deterministic core of BG20 Lemma A.5** (degree-weighted counting by blocks of `N` cells). Let the block
cells `H^{Nε}_j` meeting `B_ρ` have diameter at most `s < a` and degree sum within `E` of `6N`, with
`ρ + a ≤ 1` and `B_1 ⊆ η([-M, M])`. For `0 < r ≤ ρ`, `g` nonnegative, bounded by `L` and `L`-Lipschitz, and
points `w_k ∈ H^ε_k ∩ cl(B_r)`,

`6 ε⁻¹ ∫_{B_r \ B_a(∂B_r)} g dμ - Err ≤ ∑_{k ∈ V^ε(B_r)} deg^ε(k) g(w_k) ≤ 6 ε⁻¹ ∫_{B_a(B_r)} g dμ + Err`,

`Err = (2M/(Nε) + 5)(L E + L s (12 N + E))`. -/
theorem IsAreaParametrized.degree_counting_bounds (hpar : IsAreaParametrized μ η) {m : ℤ → ℤ → ℕ}
    {ε M ρ a s L E : ℝ} {N : ℕ} (hε : 0 < ε) (hN : 0 < N) (hM : 0 < M) (hs : 0 ≤ s) (hsa : s < a)
    (hρa : ρ + a ≤ 1) (hL : 0 ≤ L) (hE : 0 ≤ E) (hcov : ball (0 : ℂ) 1 ⊆ η '' Icc (-M) M)
    (hdiam : ∀ j : ℤ, (cell (N * ε) η j ∩ ball 0 ρ).Nonempty → diam (cell (N * ε) η j) ≤ s)
    (hdeg : ∀ j : ℤ, (cell (N * ε) η j ∩ ball 0 ρ).Nonempty →
      |(∑ k ∈ Finset.Ioc ((N : ℤ) * (j - 1)) ((N : ℤ) * j), (matedDeg m k : ℝ)) - 6 * N| ≤ E)
    {r : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) {g : ℂ → ℝ} (hg : ∀ x, 0 ≤ g x ∧ |g x| ≤ L)
    (hgL : ∀ x y, |g x - g y| ≤ L * ‖x - y‖) {w : ℤ → ℂ}
    (hw : ∀ k ∈ cellVertices ε η (ball 0 r), w k ∈ cell ε η k ∩ closure (ball 0 r)) :
    6 * ε⁻¹ * ∫ x in ball 0 r \ thickening a (frontier (ball 0 r)), g x ∂μ -
          (2 * M / (N * ε) + 5) * (L * E + L * s * (12 * N + E)) ≤
        ∑' k : cellVertices ε η (ball 0 r), (matedDeg m k : ℝ) * g (w k) ∧
      ∑' k : cellVertices ε η (ball 0 r), (matedDeg m k : ℝ) * g (w k) ≤
        6 * ε⁻¹ * ∫ x in thickening a (ball 0 r), g x ∂μ +
          (2 * M / (N * ε) + 5) * (L * E + L * s * (12 * N + E)) := by
  -- the cells of scale `ε` meeting `B_ρ` have diameter at most `s`
  have hdiamε : ∀ k : ℤ, (cell ε η k ∩ ball 0 ρ).Nonempty → diam (cell ε η k) ≤ s := by
    rintro k ⟨y, hyc, hyρ⟩
    have hsub := cell_subset_cell_blockIndex η (ε := ε) hN k
    exact (diam_mono hsub (isCompact_cell hpar.1 _ _).isBounded).trans
      (hdiam _ ⟨y, hsub hyc, hyρ⟩)
  obtain ⟨t, ht, -⟩ := hpar.exists_finset_cellVertices hε hM hsa hρa hcov hdiamε
    (ball_subset_ball hrρ)
  have hsum : ∑' k : cellVertices ε η (ball (0 : ℂ) r), (matedDeg m k : ℝ) * g (w k) =
      ∑ k ∈ t, (matedDeg m k : ℝ) * g (w k) :=
    tsum_cellVertices_eq_sum t ht (fun k => (matedDeg m k : ℝ) * g (w k))
  rw [hsum]
  have hw' : ∀ k ∈ cellVertices ε η (ball 0 r), w k ∈ cell ε η k := fun k hk => (hw k hk).1
  exact ⟨hpar.degree_counting_lower hε hN hM hs hsa hρa hL hE hcov hdiam hdeg hr hrρ hg hgL hw' t ht,
    hpar.degree_counting_upper hε hN hM hs hsa hρa hL hE hcov hdiam hdeg hrρ hg hgL hw' t ht⟩

end MatedCRT
