import MatedCRT.Steps.Sec5.GeneralIDLALowerBound
import MatedCRT.Proofs.IDLA.Measurable

/-!
# Lemma 5.2: the Chernoff bound for the lower tail of `M` (eq:expected-value-of-m, eq:concentration-inequality)

`M = ∑_{i < n} 1{τ^i_a < T^i}` is a sum of `n` independent indicators of mean `p_0 = P^0[τ_a < T_O]` under the law of
the walker sequence (`iIndepFun_infinitePi`), so `E e^{-λ M} = (1 - p_0 (1 - e^{-λ}))^n ≤ e^{-n p_0 (1 - e^{-λ})}`
and `P[M ≤ k] ≤ e^{λ k} E e^{-λ M}` (`measure_le_le_exp_mul_mgf`).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

/-- **Step** `VisitCountLowerTailStep`. -/
theorem visitCountLowerTailStep : VisitCountLowerTailStep := by
  intro m O a n l k hl
  set H : Set (ℕ → ℤ) := {x | vHitTime {a} x < vExitTime O x} with hH
  have hHm : MeasurableSet H := measurableSet_hitBeforeExit O a
  set μ := walkerSequenceLaw m 0 with hμ
  set p := hitBeforeExitProb m O a 0 with hp
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hp1 : p ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  set Y : ℕ → (ℕ → ℕ → ℤ) → ℝ := fun i xs => H.indicator 1 (xs i) with hY
  have hYm : ∀ i, Measurable (Y i) := fun i => (measurable_one.indicator hHm).comp (measurable_pi_apply i)
  have hind : iIndepFun Y μ :=
    iIndepFun_infinitePi (P := fun _ => srwLaw m 0) (X := fun _ => H.indicator 1)
      (fun _ => measurable_one.indicator hHm)
  -- `M` is the sum of the indicators
  have hM : ∀ xs, (visitCount O a xs n : ℝ) = ∑ i ∈ Finset.range n, Y i xs := by
    intro xs
    unfold visitCount
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : vHitTime {a} (xs i) < vExitTime O (xs i)
    · have hmem : xs i ∈ H := h
      simp [Y, h, hmem]
    · have hmem : xs i ∉ H := h
      simp [Y, h, hmem]
  -- the moment generating function of one indicator
  have hmgf : ∀ i, mgf (Y i) μ (-l) = 1 + (Real.exp (-l) - 1) * p := by
    intro i
    have hpt : ∀ x : ℕ → ℤ,
        Real.exp (-l * H.indicator 1 x) = 1 + (Real.exp (-l) - 1) * H.indicator 1 x := by
      intro x
      by_cases hx : x ∈ H <;> simp [hx]
    have hmap : μ.map (fun xs => xs i) = srwLaw m 0 := by
      rw [hμ]
      unfold walkerSequenceLaw
      exact Measure.infinitePi_map_eval _ i
    calc mgf (Y i) μ (-l) = ∫ xs, Real.exp (-l * H.indicator 1 (xs i)) ∂μ := rfl
      _ = ∫ x, Real.exp (-l * H.indicator 1 x) ∂(μ.map fun xs => xs i) := by
          rw [integral_map (measurable_pi_apply i).aemeasurable]
          exact (((measurable_one.indicator hHm).const_mul (-l)).exp).aestronglyMeasurable
      _ = ∫ x, (1 + (Real.exp (-l) - 1) * H.indicator 1 x) ∂(srwLaw m 0) := by
          rw [hmap]
          exact integral_congr_ae (Eventually.of_forall hpt)
      _ = 1 + (Real.exp (-l) - 1) * p := by
          have hInd : Integrable (H.indicator (1 : (ℕ → ℤ) → ℝ)) (srwLaw m 0) :=
            (integrable_const (1 : ℝ)).indicator hHm
          rw [integral_add (integrable_const _) (hInd.const_mul _),
            integral_const, integral_const_mul, integral_indicator_one hHm]
          simp [hp, hH, hitBeforeExitProb, Measure.real]
  have hsum_fun : (fun xs => ∑ i ∈ Finset.range n, Y i xs) = ∑ i ∈ Finset.range n, Y i := by
    funext xs
    rw [Finset.sum_apply]
  have hmgf_sum : mgf (fun xs => ∑ i ∈ Finset.range n, Y i xs) μ (-l) =
      (1 + (Real.exp (-l) - 1) * p) ^ n := by
    rw [hsum_fun, hind.mgf_sum hYm, Finset.prod_congr rfl fun i _ => hmgf i, Finset.prod_const,
      Finset.card_range]
  have hint : Integrable (fun xs => Real.exp (-l * ∑ i ∈ Finset.range n, Y i xs)) μ := by
    refine Integrable.of_bound ?_ 1 (Eventually.of_forall fun xs => ?_)
    · exact ((Finset.measurable_sum _ fun i _ => hYm i).const_mul (-l)).exp.aestronglyMeasurable
    · have h0 : 0 ≤ ∑ i ∈ Finset.range n, Y i xs :=
        Finset.sum_nonneg fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      nlinarith [mul_nonneg hl h0]
  have hch := measure_le_le_exp_mul_mgf (X := fun xs => ∑ i ∈ Finset.range n, Y i xs) (μ := μ) k
    (by linarith : -l ≤ 0) hint
  rw [hmgf_sum] at hch
  have hbase0 : 0 ≤ 1 + (Real.exp (-l) - 1) * p := by
    nlinarith [mul_nonneg (Real.exp_pos (-l)).le hp0]
  have hpow : (1 + (Real.exp (-l) - 1) * p) ^ n ≤ Real.exp ((n : ℝ) * ((Real.exp (-l) - 1) * p)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hbase0 (by linarith [Real.add_one_le_exp ((Real.exp (-l) - 1) * p)]) n
  have hset : {xs : ℕ → ℕ → ℤ | (visitCount O a xs n : ℝ) ≤ k} =
      {xs | ∑ i ∈ Finset.range n, Y i xs ≤ k} := by
    ext xs
    show (visitCount O a xs n : ℝ) ≤ k ↔ ∑ i ∈ Finset.range n, Y i xs ≤ k
    rw [hM xs]
  rw [hset, ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le]
  calc (μ {xs | ∑ i ∈ Finset.range n, Y i xs ≤ k}).toReal
      ≤ Real.exp (-(-l) * k) * (1 + (Real.exp (-l) - 1) * p) ^ n := hch
    _ ≤ Real.exp (-(-l) * k) * Real.exp ((n : ℝ) * ((Real.exp (-l) - 1) * p)) :=
        mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = Real.exp (l * k - n * p * (1 - Real.exp (-l))) := by
        rw [← Real.exp_add]
        congr 1
        ring

end MatedCRT
