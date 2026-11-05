import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.PathEnvelopeOn
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ExitOscillation
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ContinuumOccupation

/-!
# Lemma 3.4: continuity of the truncated occupation functional

`Φ_T(w) = ∫_{(0, T ∧ τ(w)]} g(w_t) dt`, `τ` the exit time of `B_r(z)`, is continuous for the
local uniform distance at every continuous path with a regular exit, among continuous paths,
when `g` is bounded and Hölder continuous on `B_r(z)`.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

/-- The truncated occupation functional `Φ_T(w) = ∫_{(0, T ∧ τ_D(w)]} g(w_t) dt`. -/
noncomputable def truncatedOccupationFunctional (D : Set ℂ) (g : ℂ → ℝ) (T : ℝ)
    (w : ℝ≥0 → ℂ) : ℝ :=
  ∫ t in Ioc (0 : ℝ) (min T (pathExitTime D w).toReal), g (w t.toNNReal)

/-- On a continuous path, the integrand is integrable up to the truncated exit time. -/
theorem intervalIntegrable_occupation {z : ℂ} {r : ℝ} {g : ℂ → ℝ} {M : ℝ}
    (hgM : ∀ x ∈ ball z r, |g x| ≤ M) (hgc : ContinuousOn g (ball z r))
    {w : ℝ≥0 → ℂ} (hw : Continuous w) {a : ℝ} (ha : 0 ≤ a)
    (haτ : a ≤ (pathExitTime (ball z r) w).toReal) :
    IntervalIntegrable (fun t : ℝ => g (w t.toNNReal)) volume 0 a := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha, integrableOn_Ioc_iff_integrableOn_Ioo]
  have hmem : ∀ t ∈ Ioo (0 : ℝ) a, w t.toNNReal ∈ ball z r := fun t ht =>
    path_mem_before_exit_toReal (ball z r) w ⟨ht.1, ht.2.trans_le haτ⟩
  have hcont : ContinuousOn (fun t : ℝ => g (w t.toNNReal)) (Ioo 0 a) :=
    hgc.comp (hw.comp continuous_real_toNNReal).continuousOn fun t ht => hmem t ht
  have : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) a)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; exact ENNReal.ofReal_lt_top⟩
  refine Integrable.of_bound (hcont.aestronglyMeasurable measurableSet_Ioo) M ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  exact Eventually.of_forall fun t ht => by rw [Real.norm_eq_abs]; exact hgM _ (hmem t ht)

theorem PathFunctionalContinuousWithinAt.div_const {𝒞 : Set (ℝ≥0 → ℂ)}
    {G : (ℝ≥0 → ℂ) → ℝ} {w : ℝ≥0 → ℂ} (h : PathFunctionalContinuousWithinAt 𝒞 G w) (K : ℝ) :
    PathFunctionalContinuousWithinAt 𝒞 (fun v => G v / K) w := by
  intro η hη
  rcases eq_or_ne K 0 with hK | hK
  · exact ⟨1, one_pos, fun v _ _ => by simp [hK, hη.le]⟩
  obtain ⟨ρ, hρ, hv⟩ := h (η * |K|) (mul_pos hη (abs_pos.2 hK))
  refine ⟨ρ, hρ, fun v hv𝒞 hd => ?_⟩
  rw [← sub_div, abs_div, div_le_iff₀ (abs_pos.2 hK)]
  exact hv v hv𝒞 hd

theorem ae_ne_real (c : ℝ) : ∀ᵐ x : ℝ, x ≠ c :=
  measure_mono_null (fun x hx => by simpa using hx) (measure_singleton c)

/-- **Continuity of the truncated occupation functional** at a regular exit. -/
theorem pathFunctionalContinuousWithinAt_truncatedOccupation (p : ContinuousPath ℂ) (z : ℂ)
    {r : ℝ} (hfin : ContinuousPath.exitTime (ball z r) p < ⊤)
    (hregular : ∃ᶠ t in 𝓝[>] (ContinuousPath.exitTime (ball z r) p).toNNReal,
      p t ∉ closedBall z r)
    {g : ℂ → ℝ} {M : ℝ} (hgM : ∀ x ∈ ball z r, |g x| ≤ M) {C χ : ℝ≥0} (hχ : 0 < χ)
    (hhol : HolderOnWith C χ g (ball z r)) {T : ℝ} (hT : 0 ≤ T) :
    PathFunctionalContinuousWithinAt {w | Continuous w}
      (truncatedOccupationFunctional (ball z r) g T) p := by
  intro η hη
  have hgc : ContinuousOn g (ball z r) := hhol.continuousOn hχ
  set M₀ := max M 0 with hM₀
  have hM₀0 : 0 ≤ M₀ := le_max_right _ _
  have hgM₀ : ∀ x ∈ ball z r, |g x| ≤ M₀ := fun x hx => (hgM x hx).trans (le_max_left _ _)
  -- the Hölder scale
  obtain ⟨δ₂, hδ₂, hδ₂η⟩ : ∃ δ₂ : ℝ, 0 < δ₂ ∧ (C : ℝ) * δ₂ ^ (χ : ℝ) * (T + 1) < η / 2 := by
    have h1 : Tendsto (fun t : ℝ => (C : ℝ) * t ^ (χ : ℝ) * (T + 1)) (𝓝[>] 0)
        (𝓝 ((C : ℝ) * (0 : ℝ) ^ (χ : ℝ) * (T + 1))) :=
      (((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).rpow_const
        (Or.inr (NNReal.coe_nonneg χ))).const_mul (C : ℝ)).mul_const (T + 1)
    rw [Real.zero_rpow (by exact_mod_cast hχ.ne'), mul_zero, zero_mul] at h1
    obtain ⟨t, ht, htpos⟩ :=
      ((h1.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < η / 2))).and
        self_mem_nhdsWithin).exists
    exact ⟨t, htpos, ht⟩
  set δ₁ : ℝ := η / (4 * (M₀ + 1)) with hδ₁def
  have hδ₁ : 0 < δ₁ := by positivity
  have hδ₁M : 2 * M₀ * δ₁ ≤ η / 2 := by
    rw [hδ₁def]
    rw [show 2 * M₀ * (η / (4 * (M₀ + 1))) = (η / 2) * (M₀ / (M₀ + 1)) by field_simp; ring]
    exact mul_le_of_le_one_right (by linarith) ((div_le_one (by linarith)).2 (by linarith))
  -- exit times
  have hτ := tendsto_ball_exitTime_of_localUniformDist
    (l := comap (fun v => localUniformDist v p) (𝓝 0)) p z r hfin hregular (fun v => v)
    tendsto_comap
  have hτr := (ENNReal.tendsto_toReal hfin.ne).comp hτ
  obtain ⟨ρ₁, hρ₁, hτclose⟩ := ((Metric.nhds_basis_ball.comap _).eventually_iff).1
    (Metric.tendsto_nhds.1 hτr δ₁ hδ₁)
  obtain ⟨ρ₂, hρ₂, hclose⟩ := exists_localUniformDist_bound p T.toNNReal hδ₂
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun v hv hd => ?_⟩
  change Continuous v at hv
  have hd1 : v ∈ (fun v => localUniformDist v p) ⁻¹' ball 0 ρ₁ := by
    change dist (localUniformDist v p) 0 < ρ₁
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (localUniformDist_nonneg v p)]
    exact hd.trans_le (min_le_left _ _)
  have hτvp : |(pathExitTime (ball z r) v).toReal -
      (ContinuousPath.exitTime (ball z r) p).toReal| < δ₁ := by
    have := hτclose hd1
    rwa [Real.dist_eq] at this
  have hcl := hclose v (hd.trans_le (min_le_right _ _))
  set τv := (pathExitTime (ball z r) v).toReal with hτv
  set τp := (ContinuousPath.exitTime (ball z r) p).toReal with hτp
  have hτp' : (pathExitTime (ball z r) ⇑p).toReal = τp := rfl
  set a := min T τv with ha
  set b := min T τp with hb
  have ha0 : 0 ≤ a := le_min hT ENNReal.toReal_nonneg
  have hb0 : 0 ≤ b := le_min hT ENNReal.toReal_nonneg
  set m := min a b with hm
  have hm0 : 0 ≤ m := le_min ha0 hb0
  have hab : |a - b| < δ₁ := by
    have := abs_min_sub_min_le_max T τv T τp
    rw [sub_self, abs_zero] at this
    exact (this.trans (max_le (abs_nonneg _) le_rfl)).trans_lt hτvp
  have hIv := intervalIntegrable_occupation hgM hgc hv ha0 (min_le_right _ _)
  have hIp := intervalIntegrable_occupation hgM hgc p.continuous hb0
    (by rw [hτp']; exact min_le_right _ _)
  have hma : m ≤ a := min_le_left _ _
  have hmb : m ≤ b := min_le_right _ _
  have hIv0 := hIv.mono_set (uIcc_subset_uIcc_left (by rw [uIcc_of_le ha0]; exact ⟨hm0, hma⟩))
  have hIvm := hIv.mono_set (uIcc_subset_uIcc_right (by rw [uIcc_of_le ha0]; exact ⟨hm0, hma⟩))
  have hIp0 := hIp.mono_set (uIcc_subset_uIcc_left (by rw [uIcc_of_le hb0]; exact ⟨hm0, hmb⟩))
  have hIpm := hIp.mono_set (uIcc_subset_uIcc_right (by rw [uIcc_of_le hb0]; exact ⟨hm0, hmb⟩))
  unfold truncatedOccupationFunctional
  rw [← hτv, ← ha, hτp', ← hb, ← intervalIntegral.integral_of_le ha0,
    ← intervalIntegral.integral_of_le hb0,
    ← intervalIntegral.integral_add_adjacent_intervals hIv0 hIvm,
    ← intervalIntegral.integral_add_adjacent_intervals hIp0 hIpm]
  -- the three pieces
  have hmain : |(∫ t in (0 : ℝ)..m, g (v t.toNNReal)) - ∫ t in (0 : ℝ)..m, g (p t.toNNReal)| ≤
      (C : ℝ) * δ₂ ^ (χ : ℝ) * (T + 1) := by
    rw [← intervalIntegral.integral_sub hIv0 hIp0, ← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const_ae
      (C := (C : ℝ) * δ₂ ^ (χ : ℝ)) ?_).trans ?_
    · filter_upwards [ae_ne_real m] with t htm ht
      rw [uIoc_of_le hm0] at ht
      have htm' : t < m := lt_of_le_of_ne ht.2 htm
      have hvt := path_mem_before_exit_toReal (ball z r) v
        ⟨ht.1, htm'.trans_le (hma.trans (min_le_right _ _))⟩
      have hpt := path_mem_before_exit_toReal (ball z r) p
        ⟨ht.1, by rw [hτp']; exact htm'.trans_le (hmb.trans (min_le_right _ _))⟩
      have htT : t.toNNReal ≤ T.toNNReal :=
        Real.toNNReal_le_toNNReal (htm'.le.trans (hma.trans (min_le_left _ _)))
      have hdist := hcl _ htT
      rw [Real.norm_eq_abs, ← Real.dist_eq]
      exact (hhol.dist_le hvt hpt).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow dist_nonneg hdist.le χ.2) C.2)
    · rw [sub_zero, abs_of_nonneg hm0]
      have hmT : m ≤ T + 1 := (hma.trans (min_le_left _ _)).trans (by linarith)
      exact mul_le_mul_of_nonneg_left hmT (mul_nonneg C.2 (Real.rpow_nonneg hδ₂.le _))
  have htail : ∀ (u : ℝ≥0 → ℂ) (c : ℝ), m ≤ c → c ≤ (pathExitTime (ball z r) u).toReal →
      |∫ t in m..c, g (u t.toNNReal)| ≤ M₀ * |c - m| := by
    intro u c hmc hc
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le_const_ae ?_
    filter_upwards [ae_ne_real c] with t htc ht
    rw [uIoc_of_le hmc] at ht
    have htc' : t < c := lt_of_le_of_ne ht.2 htc
    rw [Real.norm_eq_abs]
    exact hgM₀ _ (path_mem_before_exit_toReal (ball z r) u ⟨hm0.trans_lt ht.1, htc'.trans_le hc⟩)
  have h1 := htail v a hma (min_le_right _ _)
  have h2 := htail p b hmb (by rw [hτp']; exact min_le_right _ _)
  have h3 : |a - m| + |b - m| ≤ 2 * |a - b| := by
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    rcases le_total a b with h | h
    · rw [hm, min_eq_left h, abs_sub_comm]; linarith [le_abs_self (b - a)]
    · rw [hm, min_eq_right h]; linarith [le_abs_self (a - b)]
  have h4 : M₀ * (|a - m| + |b - m|) ≤ 2 * M₀ * δ₁ := by
    have := mul_le_mul_of_nonneg_left h3 hM₀0
    nlinarith
  calc |(∫ t in (0 : ℝ)..m, g (v t.toNNReal)) + (∫ t in m..a, g (v t.toNNReal)) -
        ((∫ t in (0 : ℝ)..m, g (p t.toNNReal)) + ∫ t in m..b, g (p t.toNNReal))|
      ≤ |(∫ t in (0 : ℝ)..m, g (v t.toNNReal)) - ∫ t in (0 : ℝ)..m, g (p t.toNNReal)| +
          |∫ t in m..a, g (v t.toNNReal)| + |∫ t in m..b, g (p t.toNNReal)| := by
        have e : (∫ t in (0 : ℝ)..m, g (v t.toNNReal)) + (∫ t in m..a, g (v t.toNNReal)) -
            ((∫ t in (0 : ℝ)..m, g (p t.toNNReal)) + ∫ t in m..b, g (p t.toNNReal)) =
            ((∫ t in (0 : ℝ)..m, g (v t.toNNReal)) - ∫ t in (0 : ℝ)..m, g (p t.toNNReal)) +
              (∫ t in m..a, g (v t.toNNReal)) - ∫ t in m..b, g (p t.toNNReal) := by ring
        rw [e]
        exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ η := by nlinarith

end MatedCRT
