import MatedCRT.FirstPass.Derived.LQGApproxClockRevuz
import MatedCRT.FirstPass.Derived.RevuzWeightedStart

/-!
# Gaussian tail of the occupation integrals of the approximating Liouville clocks

For a nonnegative measurable test function `f` vanishing outside the closed disc `B̄(0, n)` and the approximating
Liouville clock `A_ε(b, t) = ∫_0^t ε^{γ²/2} e^{γ h_ε(b_s)} ds` (`lqgClockApproxNN`), whose Revuz measure with respect to
Lebesgue measure is `M_ε = ε^{γ²/2} e^{γ h_ε(z)} dz` (`LatticeProb.LQG.lqgApprox`), the Lebesgue-started expectation of
the occupation integral `∫_{(0,1]} f(b_s) dA_ε(b, s)` over the starting points `|z| > R` satisfies

  `∫_{|z| > R} dz E_z[∫_{(0,1]} f(B_s) dA_ε(B, s)] ≤ (∫ f dM_ε) · γ{w : |w| > R - n}`,

with `γ` the standard planar Gaussian law. The window is Brownian time `(0, 1]`, so the tail is Gaussian and does not
depend on `ε`: under a uniform bound `sup_k ∫ f dM_{ε_k} < ∞` the left-hand side tends to `0` as `R → ∞`, uniformly
in `k`. This is the tightness in the starting point used to identify the Revuz measure of a limit of the clocks
(Fukushima–Oshima–Takeda (2011), §5.1; Revuz–Yor (1999), Chapter X, §2).

The proof uses the symmetry of planar Brownian motion with respect to Lebesgue measure at a fixed time,
`∫ 1_{|z|>R} E_z[g(B_s)] dz = ∫ g(y) P_y(|B_s| > R) dy` (`lintegral_mul_lintegral_planarLaw_eval_comm`), and the bound
`P_y(|B_s| > R) ≤ γ{w : |w| > R - n}` for `|y| ≤ n` and `s ≤ 1`.

* `planarLaw_eval_norm_gt_le`: the one-point Gaussian tail;
* `setLIntegral_norm_gt_lintegral_planarLaw_eval_le`: the tail at a fixed time `s ≤ 1`;
* `setLIntegral_norm_gt_lintegral_window_le`: the tail of the occupation integral over the window `(0, 1]`;
* `setLIntegral_norm_gt_occupation_lqgClockApproxNN_le`: the same for the approximating Liouville clock;
* `tendsto_stdPlanarGaussian_norm_gt`: `γ{w : |w| > r} → 0` as `r → ∞`;
* `tendsto_iSup_setLIntegral_norm_gt_occupation_lqgClockApproxNN`: the tail tends to `0` uniformly in `k`.
-/

set_option autoImplicit false

open MeasureTheory MarkovProcess Set Filter Topology HarmonicBalls
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- **One-point Gaussian tail.** For `|y| ≤ n` and `s ≤ 1`, `P_y(|B_s| > R) ≤ γ{w : |w| > R - n}`. -/
theorem planarLaw_eval_norm_gt_le {n R : ℝ} {y : ℂ} (hy : ‖y‖ ≤ n) {s : ℝ≥0} (hs : s ≤ 1) :
    ∫⁻ ω, {x : ℂ | R < ‖x‖}.indicator 1 (ω s) ∂planarLaw y ≤
      stdPlanarGaussian {w : ℂ | R - n < ‖w‖} := by
  have hS : MeasurableSet {x : ℂ | R < ‖x‖} := measurableSet_lt measurable_const measurable_norm
  have hT : MeasurableSet {w : ℂ | R - n < ‖w‖} := measurableSet_lt measurable_const measurable_norm
  have hv : Measurable ({x : ℂ | R < ‖x‖}.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator hS
  rw [MatedCRT.lintegral_planarLaw_eval_eq s hv y, planarGaussian_eq_map_add_sqrt_mul,
    lintegral_map hv (by fun_prop), ← lintegral_indicator_one hT]
  refine lintegral_mono fun w => ?_
  by_cases hw : R < ‖y + (Real.sqrt s : ℂ) * w‖
  · have hsq : Real.sqrt s ≤ 1 :=
      (Real.sqrt_le_sqrt (by exact_mod_cast hs : (s : ℝ) ≤ 1)).trans_eq Real.sqrt_one
    have h1 : ‖(Real.sqrt s : ℂ) * w‖ ≤ ‖w‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) hsq
    have h2 : R - n < ‖w‖ := by
      have := norm_add_le y ((Real.sqrt s : ℂ) * w)
      linarith
    have hw' : w ∈ {w : ℂ | R - n < ‖w‖} := h2
    have hw'' : y + (Real.sqrt s : ℂ) * w ∈ {x : ℂ | R < ‖x‖} := hw
    simp only [indicator_of_mem hw', indicator_of_mem hw'', Pi.one_apply, le_refl]
  · have hw'' : y + (Real.sqrt s : ℂ) * w ∉ {x : ℂ | R < ‖x‖} := hw
    simp only [indicator_of_notMem hw'', zero_le]

/-- **Gaussian tail at a fixed time.** If `g ≥ 0` is measurable and vanishes outside `B̄(0, n)`, then for `s ≤ 1`,
`∫_{|z| > R} E_z[g(B_s)] dz ≤ (∫ g) · γ{w : |w| > R - n}`. -/
theorem setLIntegral_norm_gt_lintegral_planarLaw_eval_le {n R : ℝ} {g : ℂ → ℝ≥0∞} (hg : Measurable g)
    (hgn : ∀ x : ℂ, n < ‖x‖ → g x = 0) {s : ℝ≥0} (hs : s ≤ 1) :
    ∫⁻ z in {z : ℂ | R < ‖z‖}, ∫⁻ ω, g (ω s) ∂planarLaw z ≤
      (∫⁻ x, g x) * stdPlanarGaussian {w : ℂ | R - n < ‖w‖} := by
  have hS : MeasurableSet {x : ℂ | R < ‖x‖} := measurableSet_lt measurable_const measurable_norm
  calc ∫⁻ z in {z : ℂ | R < ‖z‖}, ∫⁻ ω, g (ω s) ∂planarLaw z
      = ∫⁻ z, {x : ℂ | R < ‖x‖}.indicator 1 z * ∫⁻ ω, g (ω s) ∂planarLaw z := by
        rw [← lintegral_indicator hS]
        refine lintegral_congr fun z => ?_
        by_cases hz : z ∈ {x : ℂ | R < ‖x‖}
        · simp only [indicator_of_mem hz, Pi.one_apply, one_mul]
        · simp only [indicator_of_notMem hz, zero_mul]
    _ = ∫⁻ y, g y * ∫⁻ ω, {x : ℂ | R < ‖x‖}.indicator 1 (ω s) ∂planarLaw y :=
        MatedCRT.lintegral_mul_lintegral_planarLaw_eval_comm s (measurable_one.indicator hS) hg
    _ ≤ ∫⁻ y, g y * stdPlanarGaussian {w : ℂ | R - n < ‖w‖} := lintegral_mono fun y => by
        by_cases hy : ‖y‖ ≤ n
        · gcongr
          exact planarLaw_eval_norm_gt_le hy hs
        · simp [hgn y (not_le.1 hy)]
    _ = (∫⁻ x, g x) * stdPlanarGaussian {w : ℂ | R - n < ‖w‖} := lintegral_mul_const _ hg

/-- **Gaussian tail of the occupation integral over the window `(0, 1]`.** If `g ≥ 0` is measurable and vanishes
outside `B̄(0, n)`, then `∫_{|z| > R} E_z[∫_{(0,1]} g(B_s) ds] dz ≤ (∫ g) · γ{w : |w| > R - n}`. -/
theorem setLIntegral_norm_gt_lintegral_window_le {n R : ℝ} {g : ℂ → ℝ≥0∞} (hg : Measurable g)
    (hgn : ∀ x : ℂ, n < ‖x‖ → g x = 0) :
    ∫⁻ z in {z : ℂ | R < ‖z‖}, ∫⁻ ω, (∫⁻ s in Ioc (0 : ℝ) 1, g (ω s.toNNReal)) ∂planarLaw z ≤
      (∫⁻ x, g x) * stdPlanarGaussian {w : ℂ | R - n < ‖w‖} := by
  have hev : Measurable fun p : ℝ × ContinuousPath ℂ => p.2 p.1.toNNReal :=
    (ContinuousEval.continuous_eval.comp
      ((continuous_snd).prodMk (continuous_real_toNNReal.comp continuous_fst))).measurable
  have hjoint : Measurable fun p : ℝ × ContinuousPath ℂ => g (p.2 p.1.toNNReal) := hg.comp hev
  have hswap : ∀ z : ℂ, ∫⁻ ω, (∫⁻ s in Ioc (0 : ℝ) 1, g (ω s.toNNReal)) ∂planarLaw z =
      ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ ω, g (ω s.toNNReal) ∂planarLaw z := fun z =>
    lintegral_lintegral_swap (hjoint.comp measurable_swap).aemeasurable
  simp_rw [hswap]
  have hmeasΦ : Measurable fun q : ℂ × ℝ => ∫⁻ ω, g (ω q.2.toNNReal) ∂planarLaw q.1 :=
    measurable_lintegral_planarLaw (p := Prod.fst) measurable_fst
      (f := fun r : (ℂ × ℝ) × ContinuousPath ℂ => g (r.2 r.1.2.toNNReal))
      (hg.comp ((ContinuousEval.continuous_eval.comp
        ((continuous_snd).prodMk (continuous_real_toNNReal.comp (continuous_snd.comp continuous_fst)))).measurable))
  rw [lintegral_lintegral_swap hmeasΦ.aemeasurable]
  calc ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ z in {z : ℂ | R < ‖z‖}, ∫⁻ ω, g (ω s.toNNReal) ∂planarLaw z
      ≤ ∫⁻ _s in Ioc (0 : ℝ) 1, (∫⁻ x, g x) * stdPlanarGaussian {w : ℂ | R - n < ‖w‖} :=
        setLIntegral_mono' measurableSet_Ioc fun s hs =>
          setLIntegral_norm_gt_lintegral_planarLaw_eval_le hg hgn
            (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1.le]; exact_mod_cast hs.2)
    _ = (∫⁻ x, g x) * stdPlanarGaussian {w : ℂ | R - n < ‖w‖} := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]

/-- **Gaussian tail of the occupation integrals of the approximating Liouville clock.** If `f ≥ 0` is measurable and
vanishes outside `B̄(0, n)`, then for `ε ≥ 0` and continuous `h_ε`,
`∫_{|z| > R} E_z[∫_{(0,1]} f(B_s) dA_ε(B, s)] dz ≤ (∫ f dM_ε) · γ{w : |w| > R - n}`. -/
theorem setLIntegral_norm_gt_occupation_lqgClockApproxNN_le {γ ε : ℝ} (hε0 : 0 ≤ ε) {hε : ℝ → ℂ → ℝ}
    (hcont : Continuous (hε ε)) {n R : ℝ} {f : ℂ → ℝ≥0∞} (hf : Measurable f)
    (hfn : ∀ x : ℂ, n < ‖x‖ → f x = 0) :
    ∫⁻ z in {z : ℂ | R < ‖z‖}, ∫⁻ ω, (∫⁻ s in Ioc (0 : ℝ) 1, f (ω s.toNNReal)
        ∂(stieltjesOfNNReal fun t => lqgClockApproxNN γ hε ε t ω).measure) ∂planarLaw z ≤
      (∫⁻ x, f x ∂LatticeProb.LQG.lqgApprox γ hε ε) * stdPlanarGaussian {w : ℂ | R - n < ‖w‖} := by
  set ρ : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε x)) with hρ
  have hρc : Continuous fun x : ℂ => ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε x) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hcont))
  have hρm : Measurable ρ := ENNReal.measurable_ofReal.comp hρc.measurable
  have hω : ∀ ω : ContinuousPath ℂ, ∫⁻ s in Ioc (0 : ℝ) 1, f (ω s.toNNReal)
      ∂(stieltjesOfNNReal fun t => lqgClockApproxNN γ hε ε t ω).measure =
        ∫⁻ s in Ioc (0 : ℝ) 1, (ρ * f) (ω s.toNNReal) := fun ω => by
    rw [restrict_stieltjesOfNNReal_measure_lqgClockApproxNN hε0 hcont ω]
    exact lintegral_withDensity_eq_lintegral_mul _
      (f := fun s : ℝ => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (ω s.toNNReal))))
      (ENNReal.measurable_ofReal.comp ((continuous_clockDensity hcont ω).measurable))
      (g := fun s : ℝ => f (ω s.toNNReal))
      (hf.comp (ω.continuous.comp continuous_real_toNNReal).measurable)
  simp_rw [hω]
  have hM : ∫⁻ x, f x ∂LatticeProb.LQG.lqgApprox γ hε ε = ∫⁻ x, (ρ * f) x := by
    rw [LatticeProb.LQG.lqgApprox]
    exact lintegral_withDensity_eq_lintegral_mul _ hρm hf
  rw [hM]
  exact setLIntegral_norm_gt_lintegral_window_le (hρm.mul hf) fun x hx => by
    simp [hfn x hx]

/-- The standard planar Gaussian tail `γ{w : |w| > r}` tends to `0` as `r → ∞`. -/
theorem tendsto_stdPlanarGaussian_norm_gt :
    Tendsto (fun r : ℝ => stdPlanarGaussian {w : ℂ | r < ‖w‖}) atTop (𝓝 0) := by
  have h := tendsto_measure_iInter_atTop (μ := stdPlanarGaussian) (s := fun r : ℝ => {w : ℂ | r < ‖w‖})
    (fun r => (measurableSet_lt measurable_const measurable_norm).nullMeasurableSet)
    (fun r r' hrr' w hw => lt_of_le_of_lt hrr' hw) ⟨0, measure_ne_top _ _⟩
  have hempty : (⋂ r : ℝ, {w : ℂ | r < ‖w‖}) = ∅ := by
    exact eq_empty_of_forall_notMem fun w hw => lt_irrefl ‖w‖ (mem_iInter.1 hw ‖w‖ :)
  rw [hempty, measure_empty] at h
  exact h

/-- **The tail tends to `0` uniformly in `k`.** For clocks `A_{ε_k}` and a nonnegative measurable `f` vanishing outside
`B̄(0, n)` with `sup_k ∫ f dM_{ε_k} ≤ C < ∞`,
`sup_k ∫_{|z| > R} E_z[∫_{(0,1]} f(B_s) dA_{ε_k}(B, s)] dz → 0` as `R → ∞`. -/
theorem tendsto_iSup_setLIntegral_norm_gt_occupation_lqgClockApproxNN {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    {ε : ℕ → ℝ} (hε0 : ∀ k, 0 ≤ ε k) (hcont : ∀ k, Continuous (hε (ε k))) {n : ℝ} {f : ℂ → ℝ≥0∞}
    (hf : Measurable f) (hfn : ∀ x : ℂ, n < ‖x‖ → f x = 0) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hbound : ∀ k, ∫⁻ x, f x ∂LatticeProb.LQG.lqgApprox γ hε (ε k) ≤ C) :
    Tendsto (fun R : ℝ => ⨆ k, ∫⁻ z in {z : ℂ | R < ‖z‖}, ∫⁻ ω, (∫⁻ s in Ioc (0 : ℝ) 1, f (ω s.toNNReal)
        ∂(stieltjesOfNNReal fun t => lqgClockApproxNN γ hε (ε k) t ω).measure) ∂planarLaw z) atTop (𝓝 0) := by
  have hτ : Tendsto (fun R : ℝ => C * stdPlanarGaussian {w : ℂ | R - n < ‖w‖}) atTop (𝓝 0) := by
    have h1 := tendsto_stdPlanarGaussian_norm_gt.comp (tendsto_atTop_add_const_right atTop (-n) tendsto_id)
    have h2 := ENNReal.Tendsto.const_mul h1 (Or.inr hC)
    simpa [Function.comp_def, sub_eq_add_neg] using h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hτ (fun _ => by simp) fun R => ?_
  refine iSup_le fun k => ?_
  refine (setLIntegral_norm_gt_occupation_lqgClockApproxNN_le (hε0 k) (hcont k) hf hfn).trans ?_
  gcongr
  exact hbound k

end MatedCRT.FirstPass.Derived
