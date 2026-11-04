import MatedCRT.Steps.Sec6.ConstantOrderLowerBoundDiv

/-!
# Lemma 6.8: the random scale `𝛅'` of line 2505 (Borel-Cantelli with a measurable threshold)

* `exists_measurable_threshold`: if `∑ₙ P[Fₙᶜ] < ∞` for events `Fₙ` measurable for a `σ`-algebra `m'`, there is an
  `m'`-measurable `N : Ω → ℕ` with `ω ∈ Fₙ` for all `n ≥ N(ω)`, almost surely. The probabilities are outer measures,
  so `m'` need not be contained in the `σ`-algebra of `Ω`.
* `tsum_dyadic_ne_top`: an event family which holds with polynomially high probability has summable failure
  probabilities along the dyadic scales `2^{-n}`.
-/

namespace MatedCRT

open MeasureTheory Filter Set
open scoped ENNReal

namespace ConstantOrderDiv

/-- **Borel-Cantelli with a measurable threshold.** -/
theorem exists_measurable_threshold {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {m' : MeasurableSpace Ω}
    {F : ℕ → Set Ω} (hF : ∀ n, MeasurableSet[m'] (F n)) (hsum : ∑' n, P (F n)ᶜ ≠ ∞) :
    ∃ N : Ω → ℕ, Measurable[m'] N ∧ ∀ᵐ ω ∂P, ∀ n, N ω ≤ n → ω ∈ F n := by
  classical
  set G : ℕ → Set Ω := fun k => ⋂ n, ⋂ (_ : k ≤ n), F n with hGdef
  have hG : ∀ k, MeasurableSet[m'] (G k) := fun k =>
    MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ => hF n
  have hp : ∀ ω, ∃ k, ω ∈ G k ∨ ω ∈ (⋃ j, G j)ᶜ := by
    intro ω
    by_cases h : ω ∈ ⋃ j, G j
    · obtain ⟨j, hj⟩ := mem_iUnion.1 h
      exact ⟨j, Or.inl hj⟩
    · exact ⟨0, Or.inr h⟩
  refine ⟨fun ω => Nat.find (hp ω), ?_, ?_⟩
  · exact @measurable_find Ω m' _ _ hp fun k => (hG k).union (MeasurableSet.iUnion hG).compl
  · have hnull : P (⋃ j, G j)ᶜ = 0 := by
      have heq : (⋃ j, G j)ᶜ = limsup (fun n => (F n)ᶜ) atTop := by
        rw [limsup_eq_iInf_iSup_of_nat]
        ext ω
        simp [hGdef]
      rw [heq]
      exact measure_limsup_atTop_eq_zero hsum
    refine measure_mono_null (fun ω hω => ?_) hnull
    intro hU
    have hall : ∀ n, Nat.find (hp ω) ≤ n → ω ∈ F n := by
      intro n hn
      rcases Nat.find_spec (hp ω) with h | h
      · exact mem_iInter₂.1 h n hn
      · exact absurd hU h
    exact hω hall

/-- `((1/2)^n)^p = ((1/2)^p)^n`. -/
theorem half_pow_rpow (n : ℕ) (p : ℝ) : ((1 / 2 : ℝ) ^ n) ^ p = ((1 / 2 : ℝ) ^ p) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num),
    mul_comm]

/-- An event family with polynomially high probability has summable failure probabilities along `2^{-n}`. -/
theorem tsum_dyadic_ne_top {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {E : ℝ → Set Ω} (h : HarmonicBalls.PolyHighProb P E) :
    ∑' n : ℕ, P (E ((1 / 2 : ℝ) ^ n))ᶜ ≠ ∞ := by
  obtain ⟨p, hp, K, r₀, hr₀, hK⟩ := h
  set q : ℝ := (1 / 2 : ℝ) ^ p with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hp
  set K' : ℝ := max K 0 + (r₀ ^ p)⁻¹ with hK'
  have hbound : ∀ n : ℕ, P (E ((1 / 2 : ℝ) ^ n))ᶜ ≤ ENNReal.ofReal K' * ENNReal.ofReal q ^ n := by
    intro n
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
    have hpow : 0 ≤ ((1 / 2 : ℝ) ^ n) ^ p := by positivity
    rw [← ENNReal.ofReal_pow hq0, ← ENNReal.ofReal_mul (by positivity), ← half_pow_rpow]
    rcases lt_or_ge ((1 / 2 : ℝ) ^ n) r₀ with hn | hn
    · refine (hK _ hpos hn).trans (ENNReal.ofReal_le_ofReal ?_)
      have : K ≤ K' := (le_max_left K 0).trans (le_add_of_nonneg_right (by positivity))
      exact mul_le_mul_of_nonneg_right this hpow
    · refine prob_le_one.trans ?_
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have hr : r₀ ^ p ≤ ((1 / 2 : ℝ) ^ n) ^ p := Real.rpow_le_rpow hr₀.le hn hp.le
      have hrp : 0 < r₀ ^ p := Real.rpow_pos_of_pos hr₀ p
      calc (1 : ℝ) = (r₀ ^ p)⁻¹ * r₀ ^ p := (inv_mul_cancel₀ hrp.ne').symm
        _ ≤ (r₀ ^ p)⁻¹ * ((1 / 2 : ℝ) ^ n) ^ p := by gcongr
        _ ≤ K' * ((1 / 2 : ℝ) ^ n) ^ p := by
          gcongr
          exact le_add_of_nonneg_left (le_max_right K 0)
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.inv_ne_top.2 (tsub_pos_of_lt (ENNReal.ofReal_lt_one.2 hq1)).ne')

end ConstantOrderDiv

end MatedCRT
