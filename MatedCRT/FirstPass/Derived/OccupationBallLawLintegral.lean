import MatedCRT.FirstPass.Derived.OccupationBallLawVitali
import MatedCRT.FirstPass.Derived.LQGApproxOccupationTail

/-!
# Nonnegative-valued convergence of the mean occupation integrals, tails and vague limit

For the disc law `ballLaw R = ∫_{B(0, R)} planarLaw z dz` and the weighted approximant densities
`g_k = f ρ_k` of the dyadic approximants of the Liouville measure, this file collects the three
ingredients of the passage from the discs `B(0, R)` to the whole plane:

* `tendsto_setLIntegral_ball_windowOcc_lqgClock`: for every `R`, the nonnegative extended real
  integrals `∫_{B(0, R)} E_z[∫_{(0,1]} g_k(B_s) ds] dz` converge to
  `∫_{B(0, R)} E_z[∫ ofReal f d occupationMeasure of the limiting clock] dz`;
* `exists_tendsto_setLIntegral_compl_ball_windowOcc_le`: the contribution of `{|z| ≥ R}` is at most
  `T R`, uniformly in `k`, with `T R → 0` as `R → ∞`;
* `tendsto_lintegral_weightedApproxDensity`: `∫ g_k → ∫ ofReal f dμ` for a vague limit `μ` of the
  approximants.
-/

open MeasureTheory MarkovProcess Set Filter Topology Metric
open HarmonicBalls (lqgClockApprox IsLQGClock planarBrownianMotion)
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- The window occupation integrals integrate against the disc law over the disc. -/
theorem lintegral_windowOcc_ballLaw_eq {g : ℂ → ℝ≥0∞} (hg : Measurable g) (R : ℝ) :
    ∫⁻ b, windowOcc g b ∂ballLaw R =
      ∫⁻ z in ball (0 : ℂ) R, ∫⁻ b, windowOcc g b ∂planarLaw z := by
  unfold ballLaw
  exact Measure.lintegral_bind measurable_planarLaw.aemeasurable
    (measurable_windowOcc hg).aemeasurable

/-- First moment: the mean window occupation integral under the disc law is at most `∫ g`. -/
theorem lintegral_windowOcc_ballLaw_le {g : ℂ → ℝ≥0∞} (hg : Measurable g) (R : ℝ) :
    ∫⁻ b, windowOcc g b ∂ballLaw R ≤ ∫⁻ x, g x := by
  rw [lintegral_windowOcc_ballLaw_eq hg R]
  exact (setLIntegral_le_lintegral _ _).trans (lintegral_lintegral_windowOcc_planarLaw hg).le

/-- For a density with finite integral, the real integral of the window occupation integral under
the disc law is the extended real one. -/
theorem ofReal_integral_windowOcc_toReal_ballLaw {g : ℂ → ℝ≥0∞} (hg : Measurable g)
    (hfin : ∫⁻ x, g x ≠ ⊤) (R : ℝ) :
    ENNReal.ofReal (∫ b, (windowOcc g b).toReal ∂ballLaw R) = ∫⁻ b, windowOcc g b ∂ballLaw R := by
  have hm := measurable_windowOcc hg
  have hlt : ∫⁻ b, windowOcc g b ∂ballLaw R ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (lintegral_windowOcc_ballLaw_le hg R)
  have hi : Integrable (fun b => (windowOcc g b).toReal) (ballLaw R) :=
    integrable_toReal_of_lintegral_ne_top hm.aemeasurable hlt
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun b => ENNReal.toReal_nonneg)]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_lt_top hm hlt] with b hb
  exact ENNReal.ofReal_toReal hb.ne

/-- A function which is almost surely nonnegative under every `planarLaw z` and integrable under the
disc law has integral, in the extended reals, the iterated lower integral over the disc. -/
theorem ofReal_integral_ballLaw_eq_setLIntegral {R : ℝ} {Φ : ContinuousPath ℂ → ℝ} (hΦ : Measurable Φ)
    (hint : Integrable Φ (ballLaw R)) (hnn : ∀ z, ∀ᵐ b ∂planarLaw z, 0 ≤ Φ b) :
    ENNReal.ofReal (∫ b, Φ b ∂ballLaw R) =
      ∫⁻ z in ball (0 : ℂ) R, ∫⁻ b, ENNReal.ofReal (Φ b) ∂planarLaw z := by
  have hnn' : ∀ᵐ b ∂ballLaw R, 0 ≤ Φ b := by
    rw [ae_iff]
    have hS : MeasurableSet {b | ¬ 0 ≤ Φ b} := (measurableSet_le measurable_const hΦ).compl
    rw [ballLaw_apply R hS]
    have hz : ∀ z, planarLaw z {b | ¬ 0 ≤ Φ b} = 0 := fun z => ae_iff.1 (hnn z)
    simp only [hz, lintegral_zero]
  rw [ofReal_integral_eq_lintegral_ofReal hint hnn']
  unfold ballLaw
  exact Measure.lintegral_bind measurable_planarLaw.aemeasurable
    (ENNReal.measurable_ofReal.comp hΦ).aemeasurable

/-- **Convergence on every disc, in the extended reals.**  Under the hypotheses of
`exists_measurable_tendsto_integral_ballLaw_lqgClock`, the mean window occupation integrals of the
weighted approximant densities over `B(0, R)` converge to the mean occupation integral of the
limiting clock over `B(0, R)`. -/
theorem tendsto_setLIntegral_ball_windowOcc_lqgClock {γ : ℝ} {hE : ℝ → ℂ → ℝ}
    (hcont : ∀ k : ℕ, Continuous (hE (HarmonicBalls.dyadicScale k)))
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (hF : ∀ z, IsLQGClock planarBrownianMotion γ hE z F)
    {G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hG : IsPCAF planarLaw G)
    (hGF : ∀ z, ∀ᵐ b ∂planarLaw z, ∀ t, (G t b : ℝ) = F b t)
    {n β C : ℝ} (hβ : 0 < β) (hC0 : 0 < C)
    (hball : ∀ z : ℂ, ‖z‖ ≤ n + 1 → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ k : ℕ,
      LatticeProb.LQG.lqgApprox γ hE (LatticeProb.LQG.dyadicScale k) (ball z r) ≤
        ENNReal.ofReal (C * r ^ β))
    {f : ℂ → ℝ} (hf : Continuous f) {K : ℝ} (hfK : ∀ x, 0 ≤ f x ∧ f x ≤ K)
    (hfn : ∀ x : ℂ, n < ‖x‖ → f x = 0) (R : ℝ) :
    Tendsto (fun k : ℕ => ∫⁻ z in ball (0 : ℂ) R,
        ∫⁻ b, windowOcc (weightedApproxDensity γ hE f k) b ∂planarLaw z) atTop
      (𝓝 (∫⁻ z in ball (0 : ℂ) R, ∫⁻ b,
        ENNReal.ofReal (∫ x, f x ∂occupationMeasure (fun t => G t b) b) ∂planarLaw z)) := by
  have hf0 : ∀ x, 0 ≤ f x := fun x => (hfK x).1
  obtain ⟨Φ, hΦ, hver, hint, htend⟩ :=
    exists_measurable_tendsto_integral_ballLaw_lqgClock hcont hF hG hGF hβ hC0 hball hf hfK hfn R
  obtain ⟨M, hM, hMb⟩ := exists_lintegral_weightedApproxDensity_le (h := hE) hball hfK hfn
  have hnn : ∀ z, ∀ᵐ b ∂planarLaw z, 0 ≤ Φ b := fun z => by
    filter_upwards [hver z] with b hb
    rw [← hb]
    exact integral_nonneg fun x => hf0 x
  have e1 : ∀ k : ℕ, ∫⁻ z in ball (0 : ℂ) R,
      ∫⁻ b, windowOcc (weightedApproxDensity γ hE f k) b ∂planarLaw z =
      ENNReal.ofReal (∫ b, ∫ x, f x ∂occupationMeasure
        (fun t => lqgClockApproxNN γ hE (HarmonicBalls.dyadicScale k) t b) b ∂ballLaw R) := by
    intro k
    have hgm := measurable_weightedApproxDensity (γ := γ) (h := hE) (k := k) hf.measurable
      (hcont k).measurable
    have hfin : ∫⁻ x, weightedApproxDensity γ hE f k x ≠ ⊤ :=
      ne_top_of_le_ne_top hM (hMb k)
    have e : ∀ b : ContinuousPath ℂ, ∫ x, f x ∂occupationMeasure
        (fun t => lqgClockApproxNN γ hE (HarmonicBalls.dyadicScale k) t b) b =
        (windowOcc (weightedApproxDensity γ hE f k) b).toReal := fun b =>
      integral_occupationMeasure_lqgClockApproxNN (HarmonicBalls.dyadicScale_pos k).le (hcont k) b
        hf hf0
    simp only [e]
    rw [ofReal_integral_windowOcc_toReal_ballLaw hgm hfin R, lintegral_windowOcc_ballLaw_eq hgm R]
  have e2 : ∫⁻ z in ball (0 : ℂ) R, ∫⁻ b,
      ENNReal.ofReal (∫ x, f x ∂occupationMeasure (fun t => G t b) b) ∂planarLaw z =
      ENNReal.ofReal (∫ b, Φ b ∂ballLaw R) := by
    rw [ofReal_integral_ballLaw_eq_setLIntegral hΦ hint hnn]
    exact lintegral_congr fun z =>
      lintegral_congr_ae (Filter.EventuallyEq.fun_comp (hver z) ENNReal.ofReal)
  simp only [e1, e2]
  exact ENNReal.tendsto_ofReal htend

/-- The integral of `ofReal f` against the `k`-th approximant is the integral of the weighted
approximant density. -/
theorem lintegral_ofReal_lqgApprox_eq {γ : ℝ} {hE : ℝ → ℂ → ℝ} {f : ℂ → ℝ} (hf : Measurable f)
    (k : ℕ) (hcont : Continuous (hE (HarmonicBalls.dyadicScale k))) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂LatticeProb.LQG.lqgApprox γ hE (LatticeProb.LQG.dyadicScale k) =
      ∫⁻ x, weightedApproxDensity γ hE f k x := by
  have hρc : Continuous fun x : ℂ => LatticeProb.LQG.dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * hE (LatticeProb.LQG.dyadicScale k) x) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hcont))
  have hw := lintegral_withDensity_eq_lintegral_mul (volume : Measure ℂ)
    (f := fun x : ℂ => ENNReal.ofReal (LatticeProb.LQG.dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * hE (LatticeProb.LQG.dyadicScale k) x)))
    (ENNReal.measurable_ofReal.comp hρc.measurable)
    (g := fun x : ℂ => ENNReal.ofReal (f x)) (ENNReal.measurable_ofReal.comp hf)
  rw [LatticeProb.LQG.lqgApprox]
  refine hw.trans (lintegral_congr fun x => ?_)
  simp only [Pi.mul_apply, weightedApproxDensity]
  exact mul_comm _ _

/-- The window occupation integral of the weighted density is the occupation integral of `ofReal f`
against the Stieltjes measure of the approximating clock. -/
theorem windowOcc_weightedApproxDensity_eq {γ ε : ℝ} (hε0 : 0 ≤ ε) {hε : ℝ → ℂ → ℝ}
    (hcont : Continuous (hε ε)) (ω : ContinuousPath ℂ) {f : ℂ → ℝ} (hf : Measurable f) :
    windowOcc (fun x => ENNReal.ofReal (f x) *
        ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε x))) ω =
      ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (f (ω s.toNNReal))
        ∂(stieltjesOfNNReal fun t => lqgClockApproxNN γ hε ε t ω).measure := by
  have hev : Measurable fun s : ℝ => ω s.toNNReal :=
    (ω.continuous.comp continuous_real_toNNReal).measurable
  have hw := lintegral_withDensity_eq_lintegral_mul ((volume : Measure ℝ).restrict (Ioc 0 1))
    (f := fun s : ℝ => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (ω s.toNNReal))))
    (ENNReal.measurable_ofReal.comp (continuous_clockDensity hcont ω).measurable)
    (g := fun s : ℝ => ENNReal.ofReal (f (ω s.toNNReal)))
    ((ENNReal.measurable_ofReal.comp hf).comp hev)
  unfold windowOcc
  rw [restrict_stieltjesOfNNReal_measure_lqgClockApproxNN hε0 hcont ω]
  refine Eq.symm (hw.trans (setLIntegral_congr_fun measurableSet_Ioc fun s _ => ?_))
  simp only [Pi.mul_apply]
  exact mul_comm _ _

/-- **Uniform tail bound.**  The contribution of the exterior of the disc `B(0, R)` to the mean window
occupation integrals of the weighted approximant densities is at most `T R`, uniformly in the level
`k`, where `T R → 0` as `R → ∞`. -/
theorem exists_tendsto_setLIntegral_compl_ball_windowOcc_le {γ : ℝ} {hE : ℝ → ℂ → ℝ}
    (hcont : ∀ k : ℕ, Continuous (hE (HarmonicBalls.dyadicScale k)))
    {n β C : ℝ}
    (hball : ∀ z : ℂ, ‖z‖ ≤ n + 1 → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ k : ℕ,
      LatticeProb.LQG.lqgApprox γ hE (LatticeProb.LQG.dyadicScale k) (ball z r) ≤
        ENNReal.ofReal (C * r ^ β))
    {f : ℂ → ℝ} (hf : Measurable f) {K : ℝ} (hfK : ∀ x, 0 ≤ f x ∧ f x ≤ K)
    (hfn : ∀ x : ℂ, n < ‖x‖ → f x = 0) :
    ∃ T : ℝ → ℝ≥0∞, Tendsto T atTop (𝓝 0) ∧ ∀ (R : ℝ) (k : ℕ),
      ∫⁻ z in (ball (0 : ℂ) R)ᶜ,
        ∫⁻ b, windowOcc (weightedApproxDensity γ hE f k) b ∂planarLaw z ≤ T R := by
  obtain ⟨M, hM, hMb⟩ := exists_lintegral_weightedApproxDensity_le (h := hE) hball hfK hfn
  have hfm' : Measurable fun x => ENNReal.ofReal (f x) := ENNReal.measurable_ofReal.comp hf
  have hfn' : ∀ x : ℂ, n < ‖x‖ → ENNReal.ofReal (f x) = 0 := fun x hx => by simp [hfn x hx]
  have hbound : ∀ k, ∫⁻ x, ENNReal.ofReal (f x)
      ∂LatticeProb.LQG.lqgApprox γ hE (HarmonicBalls.dyadicScale k) ≤ M := fun k => by
    rw [dyadicScale_eq, lintegral_ofReal_lqgApprox_eq hf k (hcont k)]
    exact hMb k
  have hT := tendsto_iSup_setLIntegral_norm_gt_occupation_lqgClockApproxNN (γ := γ) (hε := hE)
    (ε := fun k => HarmonicBalls.dyadicScale k) (fun k => (HarmonicBalls.dyadicScale_pos k).le)
    hcont hfm' hfn' hM hbound
  have hsub : Tendsto (fun R : ℝ => R - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id
  refine ⟨fun R => ⨆ k : ℕ, ∫⁻ z in {z : ℂ | R - 1 < ‖z‖}, ∫⁻ ω,
    (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (f (ω s.toNNReal))
      ∂(stieltjesOfNNReal fun t => lqgClockApproxNN γ hE (HarmonicBalls.dyadicScale k) t ω).measure)
      ∂planarLaw z, hT.comp hsub, fun R k => ?_⟩
  refine le_trans ?_ (le_iSup _ k)
  have hsubset : (ball (0 : ℂ) R)ᶜ ⊆ {z : ℂ | R - 1 < ‖z‖} := fun z hz => by
    have : R ≤ ‖z‖ := by simpa [mem_ball_zero_iff] using hz
    show R - 1 < ‖z‖
    linarith
  refine (lintegral_mono_set hsubset).trans (le_of_eq ?_)
  exact lintegral_congr fun z => lintegral_congr fun ω =>
    windowOcc_weightedApproxDensity_eq (HarmonicBalls.dyadicScale_pos k).le (hcont k) ω hf

/-- **Vague limit of the weighted approximant densities.**  If `μ` is a vague limit of the dyadic
approximants, then `∫ g_k → ∫ ofReal f dμ` for continuous `0 ≤ f` vanishing off `B̄(0, n)`. -/
theorem tendsto_lintegral_weightedApproxDensity {γ : ℝ} {hE : ℝ → ℂ → ℝ} {μ : Measure ℂ}
    (hμ : LatticeProb.LQG.IsLQGLimit γ hE μ)
    (hcont : ∀ k : ℕ, Continuous (hE (HarmonicBalls.dyadicScale k)))
    {n β C : ℝ}
    (hball : ∀ z : ℂ, ‖z‖ ≤ n + 1 → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ k : ℕ,
      LatticeProb.LQG.lqgApprox γ hE (LatticeProb.LQG.dyadicScale k) (ball z r) ≤
        ENNReal.ofReal (C * r ^ β))
    {f : ℂ → ℝ} (hf : Continuous f) {K : ℝ} (hfK : ∀ x, 0 ≤ f x ∧ f x ≤ K)
    (hfn : ∀ x : ℂ, n < ‖x‖ → f x = 0) :
    Tendsto (fun k : ℕ => ∫⁻ x, weightedApproxDensity γ hE f k x) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (f x) ∂μ)) := by
  have hf0 : ∀ x, 0 ≤ f x := fun x => (hfK x).1
  obtain ⟨M, hM, hMb⟩ := exists_lintegral_weightedApproxDensity_le (h := hE) hball hfK hfn
  have hfc : HasCompactSupport f :=
    HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) n) fun x hx =>
      hfn x (by simpa [mem_closedBall_zero_iff] using hx)
  have e1 : ∀ k : ℕ, ∫⁻ x, weightedApproxDensity γ hE f k x =
      ENNReal.ofReal (∫ x, f x ∂LatticeProb.LQG.lqgApprox γ hE (LatticeProb.LQG.dyadicScale k)) := by
    intro k
    rw [← lintegral_ofReal_lqgApprox_eq hf.measurable k (hcont k)]
    have hi : Integrable f (LatticeProb.LQG.lqgApprox γ hE (LatticeProb.LQG.dyadicScale k)) := by
      rw [← lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable (ae_of_all _ hf0),
        lintegral_ofReal_lqgApprox_eq hf.measurable k (hcont k)]
      exact ne_top_of_le_ne_top hM (hMb k)
    rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hf0)]
  have e2 : ∫⁻ x, ENNReal.ofReal (f x) ∂μ = ENNReal.ofReal (∫ x, f x ∂μ) := by
    have := hμ.isLocallyFiniteMeasure
    rw [ofReal_integral_eq_lintegral_ofReal (hf.integrable_of_hasCompactSupport hfc)
      (ae_of_all _ hf0)]
  simp only [e1, e2]
  exact ENNReal.tendsto_ofReal (hμ.tendsto_integral f hf hfc)

end MatedCRT.FirstPass.Derived
