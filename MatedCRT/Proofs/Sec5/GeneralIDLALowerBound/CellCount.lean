import MatedCRT.Steps.Sec5.GeneralIDLALowerBound
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Model

/-!
# Lemma 5.2: `|V^ε(B_ρ)| ≤ ε^{-2}` with probability tending to `1` (line 2155)

From Lemma 2.8 (the cells meeting `B_ρ` have diameter `≤ ε^{1/(2+γ)²}`, so they lie in `B_R`, `R = (1 + ρ)/2`),
Lemma 2.7 at scale `δ = ε^{1/4}` (`μ_h(B_δ(z)) ≤ δ^{β⁺} ≤ 1` for `z ∈ B_{1-δ}`), a cover of `cl B_R` by
`(2⌈2/δ⌉ + 1)²` balls of radius `δ` centered on the grid `(δ/2)(ℤ + iℤ)` (`measure_closedBall_le_grid`), and the area
parametrization (the cells have mass `ε` and overlap in null sets; `ConstantOrder.cell_inter_null`):
`|F| ε ≤ μ_h(B_R) ≤ 25 δ^{-2}` for every finite `F ⊆ V^ε(B_ρ)`, hence `|V^ε(B_ρ)| ≤ 25 ε^{-3/2} ≤ ε^{-2}`.
The probability bookkeeping follows `cellVerticesBallFiniteStep` (Proofs/Sec6/ConstantOrderLowerBound/Model.lean).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

/-- The grid point `(δ/2)(i + j i)`. -/
noncomputable def gridPoint (δ : ℝ) (p : ℤ × ℤ) : ℂ := ⟨δ / 2 * p.1, δ / 2 * p.2⟩

theorem abs_round_le_of_abs_lt {x : ℝ} {M : ℕ} (hx : |x| < M) : |round x| ≤ (M : ℤ) := by
  have h := abs_sub_round x
  rw [abs_le] at h ⊢
  rw [abs_lt] at hx
  constructor
  · have h1 : (-(M : ℝ)) - 1 < (round x : ℝ) := by linarith [h.2]
    have h2 : -(M : ℤ) - 1 < round x := by exact_mod_cast h1
    omega
  · have h1 : (round x : ℝ) < (M : ℝ) + 1 := by linarith [h.1]
    have h2 : round x < (M : ℤ) + 1 := by exact_mod_cast h1
    omega

/-- `|y - (δ/2) round(2y/δ)| ≤ δ/4`. -/
theorem abs_sub_grid_le (y : ℝ) {δ : ℝ} (hδ : 0 < δ) : |y - δ / 2 * (round (2 * y / δ) : ℝ)| ≤ δ / 4 := by
  have h := abs_sub_round (2 * y / δ)
  have hid : y - δ / 2 * (round (2 * y / δ) : ℝ) = δ / 2 * (2 * y / δ - round (2 * y / δ)) := by
    rw [mul_sub, show δ / 2 * (2 * y / δ) = y by field_simp]
  rw [hid, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < δ / 2)]
  calc δ / 2 * |2 * y / δ - round (2 * y / δ)| ≤ δ / 2 * (1 / 2) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = δ / 4 := by ring

theorem round_mem_Icc {y R δ : ℝ} (hδ : 0 < δ) (hy : |y| ≤ R) (hR : R < 1) :
    round (2 * y / δ) ∈ Finset.Icc (-(⌈2 / δ⌉₊ : ℤ)) ⌈2 / δ⌉₊ := by
  have hlt : |2 * y / δ| < (⌈2 / δ⌉₊ : ℝ) := by
    rw [abs_div, abs_mul, abs_of_pos hδ, abs_two]
    calc 2 * |y| / δ < 2 / δ := by
          rw [div_lt_div_iff_of_pos_right hδ]
          linarith
      _ ≤ (⌈2 / δ⌉₊ : ℝ) := Nat.le_ceil _
  have h := abs_round_le_of_abs_lt hlt
  rw [abs_le] at h
  exact Finset.mem_Icc.2 h

/-- `cl B_R` (`R < 1`) is covered by the balls `B(z, δ)` centered at the grid points `z ∈ B_{R + δ}` with
`|i|, |j| ≤ ⌈2/δ⌉`. -/
theorem closedBall_subset_grid {R δ : ℝ} (hR : R < 1) (hδ : 0 < δ) :
    closedBall (0 : ℂ) R ⊆ ⋃ p ∈ ((Finset.Icc (-(⌈2 / δ⌉₊ : ℤ)) ⌈2 / δ⌉₊ ×ˢ
        Finset.Icc (-(⌈2 / δ⌉₊ : ℤ)) ⌈2 / δ⌉₊).filter fun p => ‖gridPoint δ p‖ < R + δ),
      ball (gridPoint δ p) δ := by
  intro w hw
  rw [mem_closedBall, dist_zero_right] at hw
  have hre : |w.re| ≤ R := (Complex.abs_re_le_norm w).trans hw
  have him : |w.im| ≤ R := (Complex.abs_im_le_norm w).trans hw
  set p : ℤ × ℤ := (round (2 * w.re / δ), round (2 * w.im / δ)) with hp
  have hdist : ‖w - gridPoint δ p‖ ≤ δ / 2 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have h1 := abs_sub_grid_le w.re hδ
    have h2 := abs_sub_grid_le w.im hδ
    simp only [Complex.sub_re, Complex.sub_im, gridPoint, hp]
    linarith
  have hnorm : ‖gridPoint δ p‖ < R + δ := by
    have : ‖gridPoint δ p‖ ≤ ‖w‖ + ‖w - gridPoint δ p‖ := by
      calc ‖gridPoint δ p‖ = ‖w - (w - gridPoint δ p)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖w‖ + ‖w - gridPoint δ p‖ := norm_sub_le _ _
    linarith
  refine mem_iUnion₂.2 ⟨p, Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨?_, ?_⟩, hnorm⟩, ?_⟩
  · exact round_mem_Icc hδ hre hR
  · exact round_mem_Icc hδ him hR
  · rw [mem_ball, dist_eq_norm]
    linarith

/-- A bound `μ(B_δ(z)) ≤ c` for the grid balls gives `μ(cl B_R) ≤ (2⌈2/δ⌉ + 1)² c`. -/
theorem measure_closedBall_le_grid (μ : Measure ℂ) {R δ c : ℝ} (hR : R < 1) (hδ : 0 < δ)
    (hc : ∀ z : ℂ, ‖z‖ < R + δ → μ (ball z δ) ≤ ENNReal.ofReal c) :
    μ (closedBall 0 R) ≤ ((2 * ⌈2 / δ⌉₊ + 1) ^ 2 : ℕ) * ENNReal.ofReal c := by
  set I := Finset.Icc (-(⌈2 / δ⌉₊ : ℤ)) ⌈2 / δ⌉₊ with hI
  set T := (I ×ˢ I).filter fun p => ‖gridPoint δ p‖ < R + δ with hT
  have hcard : I.card = 2 * ⌈2 / δ⌉₊ + 1 := by
    rw [hI, Int.card_Icc]
    have h : ((⌈2 / δ⌉₊ : ℤ) + 1 - -(⌈2 / δ⌉₊ : ℤ)) = ((2 * ⌈2 / δ⌉₊ + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [h, Int.toNat_natCast]
  calc μ (closedBall 0 R) ≤ μ (⋃ p ∈ T, ball (gridPoint δ p) δ) := measure_mono (closedBall_subset_grid hR hδ)
    _ ≤ ∑ p ∈ T, μ (ball (gridPoint δ p) δ) := measure_biUnion_finset_le _ _
    _ ≤ T.card • ENNReal.ofReal c :=
        Finset.sum_le_card_nsmul _ _ _ fun p hp => hc _ (Finset.mem_filter.1 hp).2
    _ ≤ (I ×ˢ I).card • ENNReal.ofReal c := nsmul_le_nsmul_left zero_le (Finset.card_filter_le _ _)
    _ = ((2 * ⌈2 / δ⌉₊ + 1) ^ 2 : ℕ) * ENNReal.ofReal c := by
        rw [nsmul_eq_mul, Finset.card_product, hcard, sq]

open ConstantOrder in
/-- **Step** `CellCountStep` from Lemmas 2.7 and 2.8 and the area parametrization. -/
theorem cellCountStep (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮) :
    CellCountStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS
  set e : ℝ := 1 / (2 + γ) ^ 2 with he
  have he0 : 0 < e := by positivity
  have he1 : e < 1 := by
    rw [he, div_lt_one (by positivity)]
    nlinarith
  have hA := HarmonicBalls.PolyHighProb.probTendsToOne (h28 γ hγ hγ2 e ρ he0 he1 hρ hρ1 Ω S hS)
  have hcone : IsConeField γ S.P S.hC S.hcirc S.μ := by
    unfold IsConeField
    exact ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩
  have hB := HarmonicBalls.PolyHighProb.probTendsToOne_rpow
    (h27 γ hγ hγ2 ((2 - γ) ^ 2 / 4) ((2 + γ) ^ 2 / 2 + 1) (by nlinarith) (by nlinarith) (by linarith)
      Ω S.P S.hC S.hcirc S.μ hcone) (show (0 : ℝ) < 1 / 4 by norm_num)
  have hC := probTendsToOne_of_ae (G := {ω | IsAreaParametrized (S.μ ω) (S.η ω)}) hS.isAreaParametrized
  have hδt := tendsto_rpow_nhdsGT_zero (show (0 : ℝ) < 1 / 4 by norm_num)
  refine ((hA.inter hB).inter hC).mono_ev ?_
  filter_upwards [self_mem_nhdsWithin,
    (tendsto_rpow_nhdsGT_zero he0).eventually (Iio_mem_nhds (show (0 : ℝ) < (1 - ρ) / 2 by linarith)),
    hδt.eventually (Iio_mem_nhds (show (0 : ℝ) < min ((1 - ρ) / 4) (1 / 7) by
      exact lt_min (by linarith) (by norm_num)))] with ε hε hεe hεδ ω hω
  obtain ⟨⟨hωA, hωB⟩, hωC⟩ := hω
  simp only [mem_ofPred_eq] at hωA hωB hωC ⊢
  have hε0 : 0 < ε := hε
  set δ := ε ^ (1 / 4 : ℝ) with hδdef
  have hδ0 : 0 < δ := Real.rpow_pos_of_pos hε0 _
  have hδρ : δ < (1 - ρ) / 4 := lt_of_lt_of_le hεδ (min_le_left _ _)
  have hδ7 : δ < 1 / 7 := lt_of_lt_of_le hεδ (min_le_right _ _)
  have hεδ4 : ε = δ ^ 4 := by
    rw [hδdef, ← Real.rpow_natCast, ← Real.rpow_mul hε0.le]
    norm_num
  -- the cells meeting `B_ρ` lie in `B_R`
  have hcellR : ∀ k ∈ cellVertices ε (S.η ω) (ball 0 ρ), cell ε (S.η ω) k ⊆ ball 0 ((1 + ρ) / 2) := by
    intro k hk y hy
    obtain ⟨p, hp, hpρ⟩ := hk
    have hdiam := (hωA k ⟨p, hp, hpρ⟩).2
    rw [show 2 / (2 + γ) ^ 2 - e = e by rw [he]; ring] at hdiam
    have hbdd : Bornology.IsBounded (cell ε (S.η ω) k) := (isCompact_Icc.image hωC.1).isBounded
    have hyp := dist_le_diam_of_mem hbdd hy hp
    rw [mem_ball, dist_zero_right] at hpρ ⊢
    rw [dist_eq_norm] at hyp
    have := norm_sub_norm_le y p
    linarith
  have hcellμ : ∀ k : ℤ, S.μ ω (cell ε (S.η ω) k) = ENNReal.ofReal ε := fun k => by
    unfold cell
    rw [hωC.2.2.2 _ _ (by nlinarith)]
    congr 1
    ring
  -- `μ_h(B_R) ≤ (2⌈2/δ⌉ + 1)²`
  have hμR : S.μ ω (ball 0 ((1 + ρ) / 2)) ≤ ((2 * ⌈2 / δ⌉₊ + 1) ^ 2 : ℕ) * ENNReal.ofReal 1 := by
    refine (measure_mono ball_subset_closedBall).trans
      (measure_closedBall_le_grid _ (by linarith) hδ0 fun z hz => ?_)
    have hz' : z ∈ ball (0 : ℂ) (1 - δ) := by
      rw [mem_ball, dist_zero_right]
      linarith
    exact (hωB z hz').2.trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_one hδ0.le (by linarith) (by positivity)))
  -- every finite family of cells meeting `B_ρ`
  have hfin_bound : ∀ F : Finset ℤ, (↑F : Set ℤ) ⊆ cellVertices ε (S.η ω) (ball 0 ρ) →
      (F.card : ℝ) * ε ≤ ((2 * ⌈2 / δ⌉₊ + 1) ^ 2 : ℕ) := by
    intro F hF
    have hsum : S.μ ω (⋃ k ∈ F, cell ε (S.η ω) k) = ∑ k ∈ F, S.μ ω (cell ε (S.η ω) k) := by
      refine measure_biUnion_finset₀ ?_ fun k _ =>
        (isCompact_Icc.image hωC.1).isClosed.measurableSet.nullMeasurableSet
      intro j _ k _ hjk
      show S.μ ω (cell ε (S.η ω) j ∩ cell ε (S.η ω) k) = 0
      rcases lt_or_gt_of_ne hjk with h | h
      · exact cell_inter_null hωC hε0 h
      · rw [inter_comm]
        exact cell_inter_null hωC hε0 h
    have hle : (F.card : ℝ≥0∞) * ENNReal.ofReal ε ≤ ((2 * ⌈2 / δ⌉₊ + 1) ^ 2 : ℕ) * ENNReal.ofReal 1 := by
      calc (F.card : ℝ≥0∞) * ENNReal.ofReal ε = ∑ k ∈ F, S.μ ω (cell ε (S.η ω) k) := by
            rw [Finset.sum_congr rfl fun k _ => hcellμ k, Finset.sum_const, nsmul_eq_mul]
        _ = S.μ ω (⋃ k ∈ F, cell ε (S.η ω) k) := hsum.symm
        _ ≤ S.μ ω (ball 0 ((1 + ρ) / 2)) :=
            measure_mono (iUnion₂_subset fun k hk => hcellR k (hF hk))
        _ ≤ _ := hμR
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _), mul_one,
      ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg _)] at hle
    exact hle
  -- `(2⌈2/δ⌉ + 1)² ≤ 25 δ⁻²`
  have hM : (((2 * ⌈2 / δ⌉₊ + 1) ^ 2 : ℕ) : ℝ) ≤ 25 / δ ^ 2 := by
    have hceil : (⌈2 / δ⌉₊ : ℝ) < 2 / δ + 1 := Nat.ceil_lt_add_one (by positivity)
    have h3 : 3 ≤ 1 / δ := by
      rw [le_div_iff₀ hδ0]
      linarith
    have h5 : (2 * (⌈2 / δ⌉₊ : ℝ) + 1) ≤ 5 / δ := by
      have : 2 * (2 / δ + 1) + 1 = 4 / δ + 3 := by ring
      have h4 : 4 / δ + 3 ≤ 5 / δ := by
        have : 5 / δ = 4 / δ + 1 / δ := by ring
        linarith
      linarith
    have h0 : 0 ≤ 2 * (⌈2 / δ⌉₊ : ℝ) + 1 := by positivity
    push_cast
    calc (2 * (⌈2 / δ⌉₊ : ℝ) + 1) ^ 2 ≤ (5 / δ) ^ 2 := pow_le_pow_left₀ h0 h5 2
      _ = 25 / δ ^ 2 := by ring
  have hbound : ∀ F : Finset ℤ, (↑F : Set ℤ) ⊆ cellVertices ε (S.η ω) (ball 0 ρ) →
      (F.card : ℝ) ≤ 25 / δ ^ 6 := by
    intro F hF
    have h1 := (hfin_bound F hF).trans hM
    rw [hεδ4] at h1
    rw [le_div_iff₀ (by positivity)]
    have : (F.card : ℝ) * δ ^ 6 = (F.card : ℝ) * δ ^ 4 * δ ^ 2 := by ring
    rw [this]
    calc (F.card : ℝ) * δ ^ 4 * δ ^ 2 ≤ 25 / δ ^ 2 * δ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 25 := by field_simp
  have hfinite : (cellVertices ε (S.η ω) (ball 0 ρ)).Finite := by
    by_contra hinf
    obtain ⟨n, hn⟩ := exists_nat_gt (25 / δ ^ 6)
    obtain ⟨F, hFsub, hFcard⟩ := Set.Infinite.exists_subset_card_eq hinf n
    have := hbound F hFsub
    rw [hFcard] at this
    linarith
  refine ⟨hfinite, ?_⟩
  have hcard := hbound hfinite.toFinset (by simp)
  rw [← Set.ncard_eq_toFinset_card _ hfinite] at hcard
  refine hcard.trans ?_
  have hε2 : ε ^ (-2 : ℝ) = 1 / δ ^ 8 := by
    rw [Real.rpow_neg hε0.le, Real.rpow_two, hεδ4, ← pow_mul, one_div]
  rw [hε2, div_le_div_iff₀ (by positivity) (by positivity)]
  have hδ2 : 25 * δ ^ 2 ≤ 1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hδ2 (pow_pos hδ0 6).le]

end MatedCRT
