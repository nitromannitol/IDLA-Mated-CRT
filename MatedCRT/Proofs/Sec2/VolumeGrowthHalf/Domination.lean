import MatedCRT.Steps.Sec2.VolumeGrowthHalf

/-!
# The quantum cone dominates the whole-plane GFF on the unit disk

GMS19, proof of Lemma 2.8: "If `h` is a whole-plane GFF, then `μ_{h−α log|·|}(A) ≥ μ_h(A)` for each Borel set
`A ⊂ 𝔻`." The deterministic content: if two fields have circle averages `hε' ≤ hε` on every circle `∂B_r(z)` with
`cl B_r(z) ⊆ B_1`, then their LQG measures (vague limits of `r^{γ²/2} e^{γ h_r(z)} dz` along dyadic `r`) satisfy
`μ' ≤ μ` on `B_1`.

* `integral_le_of_isLQGLimit_of_le`: `∫ f dμ' ≤ ∫ f dμ` for `f ≥ 0` continuous vanishing outside `B_ρ`, `ρ < 1` (for
  dyadic `r < 1 - ρ` the approximating densities compare on `B_ρ`).
* `measure_le_of_isLQGLimit_of_le`: `μ'(A) ≤ μ(A)` for `A ⊆ B_1` (Urysohn functions between compact and open sets, then
  inner regularity of `μ'` on open sets and outer regularity of `μ`).
* `circleAverage_log_norm_nonpos`: the average of `log |·|` over a circle in `cl B_1` is `≤ 0`, so the circle averages
  of `h̃ - γ log |·|` dominate those of `h̃` on `B_1`.
* `coneAreaDominatesWholePlaneGFFStep_of_coupling`: `ConeAreaDominatesWholePlaneGFFStep` from the coupling step
  `ConeWholePlaneCouplingStep`. Bonanno's circle-average processes and LQG areas (adapted from Leonardo Bonanno's
  lean-formalizations, https://github.com/leobon12/lean-formalizations, as ported to Lattice-Probability) are converted
  to ours by `isLQGLimit_of_isLQGAreaOf` (his `2^{-k}` is our `dyadicScale k = 2⁻¹^k`).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- Bonanno's LQG area of a circle-average process is, for a.e. sample, an LQG limit in our sense. -/
theorem isLQGLimit_of_isLQGAreaOf {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {H : ℝ → ℂ → Ω → ℝ} {μ' : Ω → Measure ℂ} (h : MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf γ H μ' P) :
    ∀ᵐ ω ∂P, IsLQGLimit γ (fun s w => H s w ω) (μ' ω) := by
  unfold MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf at h
  filter_upwards [h] with ω hω
  have heq : ∀ k : ℕ, lqgApprox γ (fun s w => H s w ω) (dyadicScale k) =
      MatedCRTHarmonic.GMSLemma27.lqgApprox γ H k ω := by
    intro k
    have hr : dyadicScale k = MatedCRTHarmonic.GMSLemma27.dyadicRadius k := by
      rw [dyadicScale, MatedCRTHarmonic.GMSLemma27.dyadicRadius, zpow_neg, zpow_natCast, inv_pow]
    rw [lqgApprox, MatedCRTHarmonic.GMSLemma27.lqgApprox, hr]
  refine ⟨hω.1, fun f hf hfc => ?_⟩
  simp only [heq]
  exact hω.2 f hf hfc

/-- **Comparison of LQG integrals.** If `hε' ≤ hε` on the circles in `B_1`, then `∫ f dμ' ≤ ∫ f dμ` for every
continuous `f ≥ 0` with compact support vanishing outside `B_ρ`, `ρ < 1`. -/
theorem integral_le_of_isLQGLimit_of_le {γ : ℝ} (hγ : 0 ≤ γ) {hε hε' : ℝ → ℂ → ℝ} {m m' : Measure ℂ}
    (hm : IsLQGLimit γ hε m) (hm' : IsLQGLimit γ hε' m') (hcont : ∀ r, 0 < r → Continuous (hε r))
    (hle : ∀ (r : ℝ) (z : ℂ), 0 < r → closedBall z r ⊆ ball (0 : ℂ) 1 → hε' r z ≤ hε r z)
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (hf0 : 0 ≤ f) {ρ : ℝ} (hρ : ρ < 1)
    (hfρ : ∀ z : ℂ, ρ ≤ ‖z‖ → f z = 0) : ∫ z, f z ∂m' ≤ ∫ z, f z ∂m := by
  refine le_of_tendsto_of_tendsto (hm'.tendsto_integral f hf hfc) (hm.tendsto_integral f hf hfc) ?_
  have hsmall : ∀ᶠ k : ℕ in atTop, dyadicScale k < 1 - ρ :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)).eventually
      (gt_mem_nhds (by linarith))
  filter_upwards [hsmall] with k hk
  have hr0 : 0 < dyadicScale k := pow_pos (by norm_num) k
  have hB : ∀ z ∉ ball (0 : ℂ) ρ, f z = 0 := fun z hz =>
    hfρ z (not_lt.mp fun h => hz (mem_ball_zero_iff.mpr h))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := lqgApprox γ hε' (dyadicScale k)) hB,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := lqgApprox γ hε (dyadicScale k)) hB]
  have hmeas : (lqgApprox γ hε' (dyadicScale k)).restrict (ball 0 ρ) ≤
      (lqgApprox γ hε (dyadicScale k)).restrict (ball 0 ρ) := by
    rw [lqgApprox, lqgApprox, restrict_withDensity measurableSet_ball, restrict_withDensity measurableSet_ball]
    refine withDensity_mono (ae_restrict_of_forall_mem measurableSet_ball fun z hz => ?_)
    have hzB : closedBall z (dyadicScale k) ⊆ ball (0 : ℂ) 1 := by
      intro x hx
      rw [mem_closedBall, dist_eq_norm] at hx
      rw [mem_ball_zero_iff] at hz ⊢
      calc ‖x‖ = ‖(x - z) + z‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
        _ < 1 := by linarith
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hle _ z hr0 hzB) hγ)) (Real.rpow_nonneg hr0.le _))
  have hloc : IsLocallyFiniteMeasure (lqgApprox γ hε (dyadicScale k)) :=
    IsLocallyFiniteMeasure.withDensity_ofReal
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (hcont _ hr0))))
  exact integral_mono_measure hmeas (ae_of_all _ fun z => hf0 z)
    (hf.integrable_of_hasCompactSupport hfc).restrict

/-- **Comparison on compact sets.** Under the hypotheses of `integral_le_of_isLQGLimit_of_le`, `μ'(K) ≤ μ(U)` for
`K` compact, `U` open, `K ⊆ U ⊆ B_1`. -/
theorem measure_compact_le_of_isLQGLimit_of_le {γ : ℝ} (hγ : 0 ≤ γ) {hε hε' : ℝ → ℂ → ℝ} {m m' : Measure ℂ}
    (hm : IsLQGLimit γ hε m) (hm' : IsLQGLimit γ hε' m') (hcont : ∀ r, 0 < r → Continuous (hε r))
    (hle : ∀ (r : ℝ) (z : ℂ), 0 < r → closedBall z r ⊆ ball (0 : ℂ) 1 → hε' r z ≤ hε r z)
    {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (hU1 : U ⊆ ball (0 : ℂ) 1) :
    m' K ≤ m U := by
  have := hm.isLocallyFiniteMeasure
  have := hm'.isLocallyFiniteMeasure
  obtain ⟨ρ, hρ1, hKρ⟩ := exists_lt_subset_ball hK.isClosed (hKU.trans hU1)
  have hVo : IsOpen (U ∩ ball (0 : ℂ) ρ) := hU.inter isOpen_ball
  obtain ⟨f, hf1, hf0, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact hK hVo.isClosed_compl
    (disjoint_compl_right_iff_subset.mpr (subset_inter hKU hKρ))
  have hfnn : 0 ≤ ⇑f := fun z => (hf01 z).1
  have hfρ : ∀ z : ℂ, ρ ≤ ‖z‖ → f z = 0 := fun z hz =>
    hf0 fun hzV => absurd (mem_ball_zero_iff.mp hzV.2) (not_lt.mpr hz)
  have hint := integral_le_of_isLQGLimit_of_le hγ hm hm' hcont hle f.continuous hfc hfnn hρ1 hfρ
  have h1 : ∀ z, K.indicator 1 z ≤ ENNReal.ofReal (f z) := by
    intro z
    by_cases hz : z ∈ K
    · rw [indicator_of_mem hz, hf1 hz]
      simp
    · rw [indicator_of_notMem hz]
      exact zero_le
  have h2 : ∀ z, ENNReal.ofReal (f z) ≤ (U ∩ ball (0 : ℂ) ρ).indicator 1 z := by
    intro z
    by_cases hz : z ∈ U ∩ ball (0 : ℂ) ρ
    · rw [indicator_of_mem hz, Pi.one_apply]
      exact ENNReal.ofReal_le_one.mpr (hf01 z).2
    · rw [indicator_of_notMem hz, hf0 hz]
      simp
  calc m' K = ∫⁻ z, K.indicator 1 z ∂m' := (lintegral_indicator_one hK.measurableSet).symm
    _ ≤ ∫⁻ z, ENNReal.ofReal (f z) ∂m' := lintegral_mono h1
    _ = ENNReal.ofReal (∫ z, f z ∂m') :=
        (ofReal_integral_eq_lintegral_ofReal (f.continuous.integrable_of_hasCompactSupport hfc)
          (ae_of_all _ hfnn)).symm
    _ ≤ ENNReal.ofReal (∫ z, f z ∂m) := ENNReal.ofReal_le_ofReal hint
    _ = ∫⁻ z, ENNReal.ofReal (f z) ∂m :=
        ofReal_integral_eq_lintegral_ofReal (f.continuous.integrable_of_hasCompactSupport hfc)
          (ae_of_all _ hfnn)
    _ ≤ ∫⁻ z, (U ∩ ball (0 : ℂ) ρ).indicator 1 z ∂m := lintegral_mono h2
    _ = m (U ∩ ball (0 : ℂ) ρ) := lintegral_indicator_one hVo.measurableSet
    _ ≤ m U := measure_mono inter_subset_left

/-- **Comparison of LQG measures on `B_1`** (GMS19, proof of Lemma 2.8). If two fields have circle averages
`hε' ≤ hε` on every circle `∂B_r(z)` with `cl B_r(z) ⊆ B_1`, and `hε` is continuous in the centre, then their LQG
measures satisfy `μ'(A) ≤ μ(A)` for every `A ⊆ B_1`. -/
theorem measure_le_of_isLQGLimit_of_le {γ : ℝ} (hγ : 0 ≤ γ) {hε hε' : ℝ → ℂ → ℝ} {m m' : Measure ℂ}
    (hm : IsLQGLimit γ hε m) (hm' : IsLQGLimit γ hε' m') (hcont : ∀ r, 0 < r → Continuous (hε r))
    (hle : ∀ (r : ℝ) (z : ℂ), 0 < r → closedBall z r ⊆ ball (0 : ℂ) 1 → hε' r z ≤ hε r z)
    {A : Set ℂ} (hA : A ⊆ ball (0 : ℂ) 1) : m' A ≤ m A := by
  have := hm.isLocallyFiniteMeasure
  have := hm'.isLocallyFiniteMeasure
  have hreg : m.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure m
  have hreg' : m'.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure m'
  rw [Set.measure_eq_iInf_isOpen A m]
  refine le_iInf fun U => le_iInf fun hAU => le_iInf fun hU => ?_
  have hV : IsOpen (U ∩ ball (0 : ℂ) 1) := hU.inter isOpen_ball
  calc m' A ≤ m' (U ∩ ball (0 : ℂ) 1) := measure_mono (subset_inter hAU hA)
    _ = ⨆ (K) (_ : K ⊆ U ∩ ball (0 : ℂ) 1) (_ : IsCompact K), m' K := hV.measure_eq_iSup_isCompact m'
    _ ≤ m (U ∩ ball (0 : ℂ) 1) := iSup_le fun K => iSup_le fun hKV => iSup_le fun hK =>
        measure_compact_le_of_isLQGLimit_of_le hγ hm hm' hcont hle hK hV hKV inter_subset_right
    _ ≤ m U := measure_mono inter_subset_left

/-- The average of `log |·|` over a circle `∂B_r(z)` with `cl B_r(z) ⊆ B_1` is `≤ 0`. -/
theorem circleAverage_log_norm_nonpos {z : ℂ} {r : ℝ} (hr : 0 ≤ r) (h : closedBall z r ⊆ ball (0 : ℂ) 1) :
    Real.circleAverage (fun x => Real.log ‖x‖) z r ≤ 0 := by
  have hθ : ∀ θ : ℝ, Real.log ‖circleMap z r θ‖ ≤ 0 := fun θ =>
    Real.log_nonpos (norm_nonneg _) (mem_ball_zero_iff.mp (h (circleMap_mem_closedBall z hr θ))).le
  have hI : 0 ≤ ∫ θ in (0 : ℝ)..2 * Real.pi, -Real.log ‖circleMap z r θ‖ :=
    intervalIntegral.integral_nonneg (by positivity) fun θ _ => neg_nonneg.mpr (hθ θ)
  rw [intervalIntegral.integral_neg] at hI
  show (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, Real.log ‖circleMap z r θ‖ ≤ 0
  exact mul_nonpos_iff.mpr (Or.inl ⟨inv_nonneg.mpr (by positivity), by linarith⟩)

/-- **The cone domination step from the coupling step**: `ConeWholePlaneCouplingStep → ConeAreaDominatesWholePlaneGFFStep`. -/
theorem coneAreaDominatesWholePlaneGFFStep_of_coupling (h : ConeWholePlaneCouplingStep) :
    ConeAreaDominatesWholePlaneGFFStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hcone
  obtain ⟨H, μ', hH, hμ', hrel⟩ := h γ hγ hγ2 Ω P hC hcirc μ hcone
  refine ⟨H, μ', hH, hμ', ?_⟩
  have hL : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ ω) := hcone.2.2
  filter_upwards [isLQGLimit_of_isLQGAreaOf hμ', hL, hcone.2.1.ae_continuousOn_circle, hrel]
    with ω hμ'ω hμω hcont hrelω
  intro A _ hA
  refine measure_le_of_isLQGLimit_of_le hγ.le hμω hμ'ω (fun r hr => ?_) (fun r z hr hz => ?_) hA
  · exact hcont.comp_continuous (continuous_const.prodMk continuous_id) fun z => ⟨hr, mem_univ _⟩
  · rw [hrelω r z hr hz]
    have h0 := circleAverage_log_norm_nonpos hr.le hz
    have h1 : γ * Real.circleAverage (fun x => Real.log ‖x‖) z r ≤ 0 :=
      mul_nonpos_iff.mpr (Or.inl ⟨hγ.le, h0⟩)
    show H r z ω ≤ H r z ω - γ * Real.circleAverage (fun x => Real.log ‖x‖) z r
    linarith

end MatedCRT
