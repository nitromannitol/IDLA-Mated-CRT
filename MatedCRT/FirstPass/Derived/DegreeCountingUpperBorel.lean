import MatedCRT.FirstPass.Derived.DegreeCountingBlockBounds

/-!
# Upper half of the degree-weighted counting bound for an arbitrary set (BG20 Lemma A.5, (A.21))

Berestycki-Gwynne (arXiv:2003.10320), Lemma A.5 is stated for an arbitrary Borel set `D ⊆ B_ρ`. The
deterministic core `IsAreaParametrized.degree_counting_upper` treats `D = B_r`; its proof only uses
`D ⊆ B_ρ`, and the same block argument gives, for every `D ⊆ B_ρ`:
if every block cell `H^{Nε}_j` meeting `B_ρ` has diameter at most `s < a` and degree sum within `E` of `6N`,
`ρ + a ≤ 1` and `B_1 ⊆ η([-M, M])`, then for `0 ≤ g ≤ L`, `L`-Lipschitz, and points `w_k ∈ H^ε_k`,

`∑_{k ∈ V^ε(D)} deg^ε(k) g(w_k) ≤ 6 ε⁻¹ ∫_{B_a(D)} g dμ + (2M/(Nε) + 5)(L E + L s (12 N + E))`.

This is the upper half of (A.21) used in the proof of BG20 Proposition 5.1 (the cell sum (5.45)).
-/

open Set Metric MeasureTheory Filter Topology HarmonicBalls

namespace MatedCRT

variable {μ : Measure ℂ} {η : ℝ → ℂ}

/-- **Upper half of the deterministic core of BG20 Lemma A.5, arbitrary `D ⊆ B_ρ`.** Under the block
hypotheses of `IsAreaParametrized.degree_counting_upper`, for every `D ⊆ B_ρ` and every finite set `t`
enumerating `V^ε(D)`, `∑_{k ∈ t} deg(k) g(w_k) ≤ 6 ε⁻¹ ∫_{B_a(D)} g dμ + (2M/δ + 5)(L E + L s (12 N + E))`,
`δ = Nε`. -/
theorem IsAreaParametrized.degree_counting_upper_of_subset (hpar : IsAreaParametrized μ η)
    {m : ℤ → ℤ → ℕ} {ε M ρ a s L E : ℝ} {N : ℕ} (hε : 0 < ε) (hN : 0 < N) (hM : 0 < M) (hs : 0 ≤ s)
    (hsa : s < a) (hρa : ρ + a ≤ 1) (hL : 0 ≤ L) (hE : 0 ≤ E)
    (hcov : ball (0 : ℂ) 1 ⊆ η '' Icc (-M) M)
    (hdiam : ∀ j : ℤ, (cell (N * ε) η j ∩ ball 0 ρ).Nonempty → diam (cell (N * ε) η j) ≤ s)
    (hdeg : ∀ j : ℤ, (cell (N * ε) η j ∩ ball 0 ρ).Nonempty →
      |(∑ k ∈ Finset.Ioc ((N : ℤ) * (j - 1)) ((N : ℤ) * j), (matedDeg m k : ℝ)) - 6 * N| ≤ E)
    {D : Set ℂ} (hDρ : D ⊆ ball 0 ρ) {g : ℂ → ℝ} (hg : ∀ x, 0 ≤ g x ∧ |g x| ≤ L)
    (hgL : ∀ x y, |g x - g y| ≤ L * ‖x - y‖) {w : ℤ → ℂ}
    (hw : ∀ k ∈ cellVertices ε η D, w k ∈ cell ε η k) (t : Finset ℤ)
    (ht : ∀ k, k ∈ t ↔ k ∈ cellVertices ε η D) :
    ∑ k ∈ t, (matedDeg m k : ℝ) * g (w k) ≤
      6 * ε⁻¹ * ∫ x in thickening a D, g x ∂μ +
        (2 * M / (N * ε) + 5) * (L * E + L * s * (12 * N + E)) := by
  classical
  set δ : ℝ := N * ε with hδ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ0 : 0 < δ := mul_pos hNr hε
  obtain ⟨F, hF, hFc⟩ := hpar.exists_finset_cellVertices hδ0 hM hsa hρa hcov hdiam hDρ
  obtain ⟨u, hu⟩ := exists_cellPoints δ η D
  have hcnt := (hpar.counting_bounds hδ0 hM hs hsa hρa hL hcov hdiam hDρ
    (fun x _ => hg x) (fun x _ y _ => hgL x y) hu).2
  have hsumF : ∑' j : cellVertices δ η D, g (u j) = ∑ j ∈ F, g (u j) :=
    tsum_cellVertices_eq_sum F hF (fun j => g (u j))
  rw [hsumF] at hcnt
  have hjρ : ∀ j ∈ F, (cell δ η j ∩ ball 0 ρ).Nonempty := fun j hj => by
    obtain ⟨y, hyc, hyD⟩ := (hF j).1 hj
    exact ⟨y, hyc, hDρ hyD⟩
  -- every vertex of `V^ε(D)` lies in a block of `V^δ(D)`
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
  have hI' : 6 * N * ∑ j ∈ F, g (u j) ≤ 6 * ε⁻¹ * ∫ x in thickening a D, g x ∂μ +
      6 * N * ((2 * M / δ + 5) * (L * s)) := by
    rw [← hNδ]
    linarith
  linarith

/-- **Upper half of BG20 (A.21), deterministic form, arbitrary `D ⊆ B_ρ`.** Under the block hypotheses
(cells of scale `Nε` meeting `B_ρ` of diameter at most `s < a`, block degree sums within `E` of `6N`,
`ρ + a ≤ 1`, `B_1 ⊆ η([-M, M])`), for every `D ⊆ B_ρ`, every `0 ≤ g ≤ L` which is `L`-Lipschitz and all
points `w_k ∈ H^ε_k`:
`∑_{k ∈ V^ε(D)} deg^ε(k) g(w_k) ≤ 6 ε⁻¹ ∫_{B_a(D)} g dμ + (2M/(Nε) + 5)(L E + L s (12 N + E))`. -/
theorem IsAreaParametrized.tsum_degree_counting_le_of_subset (hpar : IsAreaParametrized μ η)
    {m : ℤ → ℤ → ℕ} {ε M ρ a s L E : ℝ} {N : ℕ} (hε : 0 < ε) (hN : 0 < N) (hM : 0 < M) (hs : 0 ≤ s)
    (hsa : s < a) (hρa : ρ + a ≤ 1) (hL : 0 ≤ L) (hE : 0 ≤ E)
    (hcov : ball (0 : ℂ) 1 ⊆ η '' Icc (-M) M)
    (hdiam : ∀ j : ℤ, (cell (N * ε) η j ∩ ball 0 ρ).Nonempty → diam (cell (N * ε) η j) ≤ s)
    (hdeg : ∀ j : ℤ, (cell (N * ε) η j ∩ ball 0 ρ).Nonempty →
      |(∑ k ∈ Finset.Ioc ((N : ℤ) * (j - 1)) ((N : ℤ) * j), (matedDeg m k : ℝ)) - 6 * N| ≤ E)
    {D : Set ℂ} (hDρ : D ⊆ ball 0 ρ) {g : ℂ → ℝ} (hg : ∀ x, 0 ≤ g x ∧ |g x| ≤ L)
    (hgL : ∀ x y, |g x - g y| ≤ L * ‖x - y‖) {w : ℤ → ℂ}
    (hw : ∀ k ∈ cellVertices ε η D, w k ∈ cell ε η k) :
    ∑' k : cellVertices ε η D, (matedDeg m k : ℝ) * g (w k) ≤
      6 * ε⁻¹ * ∫ x in thickening a D, g x ∂μ +
        (2 * M / (N * ε) + 5) * (L * E + L * s * (12 * N + E)) := by
  -- the cells of scale `ε` meeting `B_ρ` have diameter at most `s`
  have hdiamε : ∀ k : ℤ, (cell ε η k ∩ ball 0 ρ).Nonempty → diam (cell ε η k) ≤ s := by
    rintro k ⟨y, hyc, hyρ⟩
    have hsub := cell_subset_cell_blockIndex η (ε := ε) hN k
    exact (diam_mono hsub (isCompact_cell hpar.1 _ _).isBounded).trans
      (hdiam _ ⟨y, hsub hyc, hyρ⟩)
  obtain ⟨t, ht, -⟩ := hpar.exists_finset_cellVertices hε hM hsa hρa hcov hdiamε hDρ
  rw [tsum_cellVertices_eq_sum t ht (fun k => (matedDeg m k : ℝ) * g (w k))]
  exact hpar.degree_counting_upper_of_subset hε hN hM hs hsa hρa hL hE hcov hdiam hdeg hDρ hg hgL hw t ht

end MatedCRT
