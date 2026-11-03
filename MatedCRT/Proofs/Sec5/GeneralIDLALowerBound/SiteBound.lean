import MatedCRT.Steps.Sec5.GeneralIDLALowerBound
import MatedCRT.Proofs.IDLA.Basic

/-!
# Lemma 5.2: the one-site bound (eq:upper-bound, eq:concentration-inequality, lines 2170-2227)

* `missedSiteVisitStep`: if `a` is not in the cluster after `n` walkers, every walker which hits `a` before exiting
  `O` does so after leaving the cluster of the previous walkers (`M ≤ L`, line 2170).
* `quenchedSiteBound_of_steps`: `QuenchedSiteBoundStep` from `M ≤ L` on `{a ∉ A(n)}` and the Chernoff bounds for the
  lower tail of `M` and the upper tail of `L`, with `k = (1 + t/2) μ`, `λ = t/8`, `c = t²/32`, `t = min(𝔰, 1)`.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- If `a` is in none of the clusters `C i`, `i < n`, then `M ≤ L`. -/
theorem visitCount_le_lateVisitCount (C : ℕ → Set ℤ) (O : Set ℤ) (a : ℤ) (xs : ℕ → ℕ → ℤ) (n : ℕ)
    (hC : ∀ i < n, a ∉ C i) : visitCount O a xs n ≤ lateVisitCount C O a xs n := by
  unfold visitCount lateVisitCount
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
  refine ⟨hi.1, ?_, hi.2⟩
  by_contra hlt
  rw [not_le] at hlt
  have hne : vHitTime {a} (xs i) ≠ ⊤ := ne_top_of_lt hi.2
  have hk : vHitTime {a} (xs i) = ((vHitTime {a} (xs i)).toNat : ℕ∞) := (ENat.natCast_toNat hne).symm
  have hxk : xs i (vHitTime {a} (xs i)).toNat = a := apply_vHitTime_eq hk
  rw [hk] at hlt
  have hmem := mem_of_lt_vExitTime hlt
  rw [hxk] at hmem
  exact hC i hi.1 hmem

/-- **Step** `MissedSiteVisitStep` (eq:upper-bound, line 2170). -/
theorem missedSiteVisitStep : MissedSiteVisitStep := by
  intro O a xs n
  exact ⟨fun ha => visitCount_le_lateVisitCount _ O a xs n fun i hi hai => ha (idlaCluster_mono xs hi.le hai),
    fun ha => visitCount_le_lateVisitCount _ O a xs n fun i hi hai =>
      ha (stoppedIDLACluster_mono O xs hi.le hai)⟩

/-- `e^{-λ} ≤ 1 - λ + λ²` for `0 ≤ λ ≤ 1`. -/
theorem exp_neg_le_quadratic {l : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) : Real.exp (-l) ≤ 1 - l + l ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le (x := -l) (by rw [abs_neg, abs_of_nonneg h0]; exact h1)
  have h' := (abs_le.1 h).2
  rw [neg_sq] at h'
  linarith

/-- `e^{λ} ≤ 1 + λ + λ²` for `0 ≤ λ ≤ 1`. -/
theorem exp_le_quadratic {l : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) : Real.exp l ≤ 1 + l + l ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le (x := l) (by rw [abs_of_nonneg h0]; exact h1)
  have h' := (abs_le.1 h).2
  linarith

/-- **Step** `QuenchedSiteBoundStep` from `MissedSiteVisitStep` and the Chernoff bounds for `M` and `L`
(eq:upper-bound with `k = (1 + t/2) μ`; eq:concentration-inequality). -/
theorem quenchedSiteBound_of_steps (hMs : MissedSiteVisitStep) (hMt : VisitCountLowerTailStep)
    (hLt : LateVisitUpperTailStep) : QuenchedSiteBoundStep := by
  intro s hs
  have ht0 : 0 < min s 1 := lt_min hs one_pos
  have ht1 : min s 1 ≤ 1 := min_le_right _ _
  have hts : min s 1 ≤ s := min_le_left _ _
  set t := min s 1 with ht
  refine ⟨t ^ 2 / 32, div_pos (pow_pos ht0 2) (by norm_num), fun m O a n hsum hn => ?_⟩
  set μ := ∑' z : O, hitBeforeExitProb m O a z with hμ
  set p0 := hitBeforeExitProb m O a 0 with hp0
  have hμ0 : 0 ≤ μ := tsum_nonneg fun z => ENNReal.toReal_nonneg
  have hp00 : 0 ≤ p0 := ENNReal.toReal_nonneg
  have hn' : (1 + t) * μ ≤ n * p0 := (mul_le_mul_of_nonneg_right (by linarith) hμ0).trans hn
  have hl0 : 0 ≤ t / 8 := div_nonneg ht0.le (by norm_num)
  have hl1 : t / 8 ≤ 1 := by linarith
  have hexp1 := exp_neg_le_quadratic hl0 hl1
  have hexp2 := exp_le_quadratic hl0 hl1
  -- the lower tail of `M`
  have hb1 : t / 8 * ((1 + t / 2) * μ) - n * p0 * (1 - Real.exp (-(t / 8))) ≤ -(t ^ 2 / 32 * μ) := by
    have hnp : 0 ≤ (n : ℝ) * p0 := mul_nonneg (Nat.cast_nonneg _) hp00
    have hq0 : 0 ≤ t / 8 - (t / 8) ^ 2 := by nlinarith [mul_nonneg hl0 (by linarith : (0 : ℝ) ≤ 1 - t / 8)]
    have h1 : (1 + t) * μ * (t / 8 - (t / 8) ^ 2) ≤ n * p0 * (1 - Real.exp (-(t / 8))) :=
      mul_le_mul hn' (by linarith) hq0 hnp
    nlinarith [mul_nonneg (mul_nonneg hμ0 (sq_nonneg t)) (sub_nonneg.2 ht1)]
  -- the upper tail of `L`
  have hb2 : -(t / 8 * ((1 + t / 2) * μ)) + (Real.exp (t / 8) - 1) * μ ≤ -(t ^ 2 / 32 * μ) := by
    have h2 : (Real.exp (t / 8) - 1) * μ ≤ (t / 8 + (t / 8) ^ 2) * μ :=
      mul_le_mul_of_nonneg_right (by linarith) hμ0
    nlinarith [mul_nonneg hμ0 (sq_nonneg t)]
  have hM := hMt m O a n (t / 8) ((1 + t / 2) * μ) hl0
  obtain ⟨hL1, hL2⟩ := hLt m O a n (t / 8) ((1 + t / 2) * μ) hl0 hsum
  have hfin : ∀ (Lc : (ℕ → ℕ → ℤ) → ℕ) (E : Set (ℕ → ℕ → ℤ)),
      (∀ xs ∈ E, visitCount O a xs n ≤ Lc xs) →
      walkerSequenceLaw m 0 {xs | (1 + t / 2) * μ ≤ (Lc xs : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(t / 8 * ((1 + t / 2) * μ)) + (Real.exp (t / 8) - 1) * μ)) →
      walkerSequenceLaw m 0 E ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / 32 * μ))) := by
    intro Lc E hE hL
    calc walkerSequenceLaw m 0 E
        ≤ walkerSequenceLaw m 0 ({xs | (visitCount O a xs n : ℝ) ≤ (1 + t / 2) * μ} ∪
            {xs | (1 + t / 2) * μ ≤ (Lc xs : ℝ)}) := by
          apply measure_mono
          intro xs hxs
          by_cases hk : (visitCount O a xs n : ℝ) ≤ (1 + t / 2) * μ
          · exact Or.inl hk
          · have h' : (visitCount O a xs n : ℝ) ≤ Lc xs := by exact_mod_cast hE xs hxs
            exact Or.inr (show (1 + t / 2) * μ ≤ (Lc xs : ℝ) by linarith)
      _ ≤ walkerSequenceLaw m 0 {xs | (visitCount O a xs n : ℝ) ≤ (1 + t / 2) * μ} +
            walkerSequenceLaw m 0 {xs | (1 + t / 2) * μ ≤ (Lc xs : ℝ)} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (Real.exp (-(t ^ 2 / 32 * μ))) + ENNReal.ofReal (Real.exp (-(t ^ 2 / 32 * μ))) :=
          add_le_add (hM.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hb1)))
            (hL.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hb2)))
      _ = ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / 32 * μ))) := by
          rw [two_mul, ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
  exact ⟨hfin (fun xs => lateVisitCount (idlaCluster xs) O a xs n) _
      (fun xs hxs => (hMs O a xs n).1 hxs) hL1,
    hfin (fun xs => lateVisitCount (stoppedIDLACluster O xs) O a xs n) _
      (fun xs hxs => (hMs O a xs n).2 hxs) hL2⟩

end MatedCRT
