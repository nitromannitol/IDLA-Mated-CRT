import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Threshold

/-!
# Lemma 2, eq (8): the ball-mass lower bound with a field-measurable scale

, Lemma 2 (lines 186-200). Eq (8): `μ_h(B_t(y)) ≥ c_v t^b` for `y ∈ cl B_ρ` and
`0 < t < t_*`, with `c_v = 4^{-b}` and a field-measurable `t_*`.

* `BallMassLower.ballMass_lower_of_polyHighProb`: the lower bound at all centres of the dyadic-scale events (hypothesis
  `hlow`, the lower half of `VolumeGrowthStmt` with exponent `b`) gives the bound at all centres of `closedBall 0 ρ` and all
  small radii. The argument uses a countable dense set of centres in `ball 0 ρ₁`, a dyadic scale `s ∈ [t/4, t/2)`, and the
  inclusion `ball q s ⊆ ball y t` for `dist y q < s / 2`. The threshold is field-measurable by
  `ConstantOrderDiv.exists_measurable_threshold` (Borel-Cantelli with a measurable threshold).
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace MatedCRT

namespace BallMassLower

/-- **Lemma 2, eq (8)** (Lemma 2 item 1): lower ball-mass bound at a field-measurable scale, `c_v = 4^{-b}`. -/
theorem ballMass_lower_of_polyHighProb {Ω : Type*} {m' : MeasurableSpace Ω} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) {ρ ρ₁ b : ℝ} (hρ : 0 < ρ) (hρρ₁ : ρ < ρ₁) (hρ₁ : ρ₁ < 1) (hb : 0 < b)
    (hlow : HarmonicBalls.PolyHighProb P fun δ =>
      {ω | ∀ z ∈ Metric.ball (0 : ℂ) (1 - δ), ENNReal.ofReal (δ ^ b) ≤ μ ω (Metric.ball z δ)})
    (hμ : ∀ (q : ℂ) (s : ℝ), Measurable[m'] fun ω => μ ω (Metric.ball q s)) :
    ∃ tStar : Ω → ℝ, Measurable[m'] tStar ∧ ∀ᵐ ω ∂P, 0 < tStar ω ∧
      ∀ y ∈ closedBall (0 : ℂ) ρ, ∀ t : ℝ, 0 < t → t < tStar ω →
        ENNReal.ofReal ((t / 4) ^ b) ≤ μ ω (Metric.ball y t) := by
  obtain ⟨D, hDc, hDd⟩ : ∃ s : Set ℂ, s.Countable ∧ Dense s := TopologicalSpace.exists_countable_dense ℂ
  have hD₁c : (D ∩ Metric.ball (0 : ℂ) ρ₁).Countable := hDc.mono inter_subset_left
  have : Countable ↥(D ∩ Metric.ball (0 : ℂ) ρ₁) := hD₁c.to_subtype
  let E : ℕ → Set Ω := fun n => {ω | ∀ z ∈ Metric.ball (0 : ℂ) (1 - (1 / 2 : ℝ) ^ n),
    ENNReal.ofReal (((1 / 2 : ℝ) ^ n) ^ b) ≤ μ ω (Metric.ball z ((1 / 2 : ℝ) ^ n))}
  let F : ℕ → Set Ω := fun n => {ω | 1 - ρ₁ ≤ (1 / 2 : ℝ) ^ n ∨
    ∀ q : ↥(D ∩ Metric.ball (0 : ℂ) ρ₁),
      ENNReal.ofReal (((1 / 2 : ℝ) ^ n) ^ b) ≤ μ ω (Metric.ball (q : ℂ) ((1 / 2 : ℝ) ^ n))}
  have hsum0 : ∑' n : ℕ, P (E n)ᶜ ≠ ∞ := ConstantOrderDiv.tsum_dyadic_ne_top hlow
  have hEF : ∀ n, E n ⊆ F n := by
    intro n ω hω
    by_cases h : 1 - ρ₁ ≤ (1 / 2 : ℝ) ^ n
    · exact Or.inl h
    · refine Or.inr fun q => hω (q : ℂ) ?_
      have hq : (q : ℂ) ∈ Metric.ball (0 : ℂ) ρ₁ := q.2.2
      rw [mem_ball_zero_iff] at hq ⊢
      linarith [not_le.1 h]
  have hFm : ∀ n, MeasurableSet[m'] (F n) := by
    intro n
    refine (MeasurableSet.const _).union ?_
    have hcount : MeasurableSet[m'] (⋂ q : ↥(D ∩ Metric.ball (0 : ℂ) ρ₁),
        {ω | ENNReal.ofReal (((1 / 2 : ℝ) ^ n) ^ b) ≤ μ ω (Metric.ball (q : ℂ) ((1 / 2 : ℝ) ^ n))}) :=
      MeasurableSet.iInter fun q => measurableSet_le measurable_const (hμ _ _)
    rw [← Set.ofPred_forall] at hcount
    exact hcount
  have hFsum : ∑' n : ℕ, P (F n)ᶜ ≠ ∞ :=
    ne_top_of_le_ne_top hsum0 (ENNReal.tsum_le_tsum fun n => measure_mono (compl_subset_compl.2 (hEF n)))
  obtain ⟨N, hNm, hN⟩ := ConstantOrderDiv.exists_measurable_threshold P hFm hFsum
  have hpow : Measurable[m'] fun ω => (1 / 2 : ℝ) ^ N ω :=
    (measurable_from_nat (f := fun n : ℕ => (1 / 2 : ℝ) ^ n)).comp hNm
  refine ⟨fun ω => min (min ((1 / 2 : ℝ) ^ N ω) (ρ₁ - ρ)) (1 - ρ₁),
    (hpow.min measurable_const).min measurable_const, ?_⟩
  filter_upwards [hN] with ω hω
  have hS1 : min (min ((1 / 2 : ℝ) ^ N ω) (ρ₁ - ρ)) (1 - ρ₁) ≤ (1 / 2 : ℝ) ^ N ω :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hS2 : min (min ((1 / 2 : ℝ) ^ N ω) (ρ₁ - ρ)) (1 - ρ₁) ≤ ρ₁ - ρ :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hS3 : min (min ((1 / 2 : ℝ) ^ N ω) (ρ₁ - ρ)) (1 - ρ₁) ≤ 1 - ρ₁ := min_le_right _ _
  have hSpos : 0 < min (min ((1 / 2 : ℝ) ^ N ω) (ρ₁ - ρ)) (1 - ρ₁) :=
    lt_min (lt_min (by positivity) (by linarith)) (by linarith)
  refine ⟨hSpos, fun y hy t ht hts => ?_⟩
  set tS := min (min ((1 / 2 : ℝ) ^ N ω) (ρ₁ - ρ)) (1 - ρ₁) with htS
  have ht1 : t < 1 := by linarith
  -- a dyadic scale `s = (1/2)^(n+1)` with `t/4 ≤ s < t/2`
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (x := 2 / t) (y := (2 : ℝ))
    ((one_le_div ht).2 (by linarith)) (by norm_num)
  have hP : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  have hs2 : (1 / 2 : ℝ) ^ (n + 1) * 2 ^ (n + 1) = 1 := by
    rw [← mul_pow]; norm_num
  rw [div_lt_iff₀ ht] at hn2
  rw [le_div_iff₀ ht] at hn1
  have hn2' : 2 < t * 2 ^ (n + 1) := by linarith
  have hn1' : t * 2 ^ (n + 1) ≤ 4 := by rw [pow_succ]; linarith
  set s : ℝ := (1 / 2 : ℝ) ^ (n + 1) with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  have hs_lt : s < t / 2 := lt_of_mul_lt_mul_right (by linarith [hs2, hn2']) hP.le
  have hs_ge : t / 4 ≤ s := le_of_mul_le_mul_right (by linarith [hs2, hn1']) hP
  -- the index is beyond the threshold `N ω`
  have hNn : N ω ≤ n + 1 := by
    by_contra hlt
    have hlt' : n + 1 < N ω := not_le.1 hlt
    have h1 : (1 / 2 : ℝ) ^ N ω ≤ (1 / 2 : ℝ) ^ (n + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hlt'.le
    linarith
  have hFmem : ω ∈ F (n + 1) := hω (n + 1) hNn
  have hsS : s < 1 - ρ₁ := by linarith
  have hsD : s / 2 < ρ₁ - ρ := by linarith
  have hFmem' : ∀ q : ↥(D ∩ Metric.ball (0 : ℂ) ρ₁), ENNReal.ofReal (s ^ b) ≤ μ ω (Metric.ball (q : ℂ) s) := by
    rcases hFmem with h | h
    · exact absurd h (not_le.2 hsS)
    · exact h
  -- a countable centre `q` within `s/2` of `y`
  obtain ⟨q, hqD, hqd⟩ := hDd.exists_dist_lt y (by positivity : (0 : ℝ) < s / 2)
  have hqball : q ∈ Metric.ball (0 : ℂ) ρ₁ := by
    rw [mem_ball_zero_iff]
    have htri : ‖q‖ ≤ ‖q - y‖ + ‖y‖ := by
      have := norm_add_le (q - y) y
      rwa [sub_add_cancel] at this
    have hyn : ‖y‖ ≤ ρ := mem_closedBall_zero_iff.1 hy
    have hqy : ‖q - y‖ < s / 2 := by rw [← dist_eq_norm, dist_comm]; exact hqd
    linarith
  have hsub : Metric.ball (q : ℂ) s ⊆ ball y t := by
    intro x hx
    rw [mem_ball] at hx ⊢
    have h1 := dist_triangle x q y
    have hqy : dist q y < s / 2 := by rw [dist_comm]; exact hqd
    linarith
  calc ENNReal.ofReal ((t / 4) ^ b) ≤ ENNReal.ofReal (s ^ b) :=
        ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by linarith) hs_ge hb.le)
    _ ≤ μ ω (ball q s) := hFmem' ⟨q, ⟨hqD, hqball⟩⟩
    _ ≤ μ ω (Metric.ball y t) := measure_mono hsub

end BallMassLower

end MatedCRT

#print axioms MatedCRT.BallMassLower.ballMass_lower_of_polyHighProb
