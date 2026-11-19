import MatedCRT.FirstPass.Derived.LQGClockVersionPCAF
import MatedCRT.FirstPass.Derived.LQGLimitClockShiftAdditive
import MatedCRT.FirstPass.Derived.LQGClockApproxAdapted
import MatedCRT.FirstPass.Derived.LQGClockApproxMeasurable
import MatedCRT.FirstPass.Derived.RevuzLintegral
import MatedCRT.FirstPass.Derived.RevuzPositive
import MatedCRT.FirstPass.Derived.RevuzLebesgueInvariance

/-!
# The approximating Liouville clocks are positive continuous additive functionals with Revuz measure `ρ_ε dz`

For a continuous circle-average function `h_ε` and `ε ≥ 0`, the clock `A_ε(b, t) = ∫_0^t ε^{γ²/2} e^{γ h_ε(b_s)} ds`
(`lqgClockApprox`), read in `ℝ≥0`, is a positive continuous additive functional of planar Brownian motion
(`IsPCAF planarLaw`), adapted to the natural filtration, whose Stieltjes measure is `ρ_ε(b_s) ds` on `(0, ∞)` with
`ρ_ε = ε^{γ²/2} e^{γ h_ε}`.  By the stationarity of Lebesgue measure for planar Brownian motion, its Revuz measure
with respect to Lebesgue measure is the approximating measure `ρ_ε dz` (`LatticeProb.LQG.lqgApprox`)
(Fukushima–Oshima–Takeda (2011), (5.1.13); Revuz–Yor (1999), Chapter X, §2).

* `lqgClockApproxNN`: the clock in `ℝ≥0`;
* `stieltjesOfNNReal_measure_lqgClockApprox`: its Stieltjes measure is the density `ρ_ε(b_s) ds` on `(0, ∞)`;
* `isPCAF_lqgClockApproxNN`: `IsPCAF planarLaw (lqgClockApproxNN γ hε ε)`;
* `revuz_lqgClockApproxNN`: `revuz planarLaw (lqgClockApproxNN γ hε ε) = lqgApprox γ hε ε`.
-/

set_option autoImplicit false

open MeasureTheory MarkovProcess Set Filter Topology
open HarmonicBalls (lqgClockApprox)
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- The approximating Liouville clock `t ↦ ∫_0^t ε^{γ²/2} e^{γ h_ε(b_s)} ds`, read in `ℝ≥0` (it is nonnegative for
`ε ≥ 0`). -/
noncomputable def lqgClockApproxNN (γ : ℝ) (hε : ℝ → ℂ → ℝ) (ε : ℝ) (t : ℝ≥0) (b : ContinuousPath ℂ) : ℝ≥0 :=
  (lqgClockApprox γ hε ε b t).toNNReal

theorem coe_lqgClockApproxNN {γ ε : ℝ} (hε0 : 0 ≤ ε) (hε : ℝ → ℂ → ℝ) (t : ℝ≥0) (b : ContinuousPath ℂ) :
    (lqgClockApproxNN γ hε ε t b : ℝ) = lqgClockApprox γ hε ε b t :=
  Real.coe_toNNReal _ (LQGLimitClockShift.lqgClockApprox_nonneg hε0 hε b t)

theorem continuous_clockDensity {γ ε : ℝ} {hε : ℝ → ℂ → ℝ} (hcont : Continuous (hε ε)) (b : ContinuousPath ℂ) :
    Continuous fun s : ℝ => ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (b s.toNNReal)) := by
  have hb : Continuous fun s : ℝ => b s.toNNReal := b.continuous.comp continuous_real_toNNReal
  exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (hcont.comp hb)))

theorem continuous_lqgClockApproxNN {γ ε : ℝ} {hε : ℝ → ℂ → ℝ} (hcont : Continuous (hε ε))
    (b : ContinuousPath ℂ) : Continuous fun t : ℝ≥0 => lqgClockApproxNN γ hε ε t b :=
  continuous_real_toNNReal.comp
    (LQGClockApproxMeasurable.continuous_lqgClockApprox_of_intervalIntegrable fun u v =>
      (continuous_clockDensity hcont b).intervalIntegrable u v)

theorem monotone_lqgClockApproxNN {γ ε : ℝ} (hε0 : 0 ≤ ε) {hε : ℝ → ℂ → ℝ} (hcont : Continuous (hε ε))
    (b : ContinuousPath ℂ) : Monotone fun t : ℝ≥0 => lqgClockApproxNN γ hε ε t b :=
  fun _ _ h => Real.toNNReal_mono (LQGLimitClockShift.monotone_lqgClockApprox hε0 hcont b h)

/-- **The Stieltjes measure of the approximating Liouville clock** is `ε^{γ²/2} e^{γ h_ε(b_s)} ds` on `(0, ∞)`. -/
theorem stieltjesOfNNReal_measure_lqgClockApproxNN {γ ε : ℝ} (hε0 : 0 ≤ ε) {hε : ℝ → ℂ → ℝ}
    (hcont : Continuous (hε ε)) (b : ContinuousPath ℂ) :
    (stieltjesOfNNReal fun t => lqgClockApproxNN γ hε ε t b).measure =
      ((volume : Measure ℝ).restrict (Ioi 0)).withDensity fun s =>
        ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (b s.toNNReal))) := by
  have hm := monotone_lqgClockApproxNN (γ := γ) hε0 hcont b
  have hc := continuous_lqgClockApproxNN (γ := γ) hcont b
  have hφ := continuous_clockDensity (γ := γ) hcont b
  have hφ0 : ∀ s : ℝ, 0 ≤ ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (b s.toNNReal)) := fun s =>
    mul_nonneg (Real.rpow_nonneg hε0 _) (Real.exp_pos _).le
  refine Measure.ext_of_Ioc _ _ fun x y hxy => ?_
  rw [stieltjesOfNNReal_measure_Ioc hm hc, withDensity_apply _ measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, Set.Ioc_inter_Ioi]
  have hA : ∀ t : ℝ≥0, (lqgClockApproxNN γ hε ε t b : ℝ) =
      ∫ s in (0 : ℝ)..(t : ℝ), ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (b s.toNNReal)) :=
    fun t => coe_lqgClockApproxNN hε0 hε t b
  have hint : ∀ u v : ℝ, IntervalIntegrable
      (fun s : ℝ => ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (b s.toNNReal))) volume u v :=
    fun u v => hφ.intervalIntegrable u v
  rcases le_or_gt y 0 with hy | hy
  · have hx : x.toNNReal = 0 := Real.toNNReal_of_nonpos (hxy.le.trans hy)
    have hy' : y.toNNReal = 0 := Real.toNNReal_of_nonpos hy
    rw [hx, hy', sub_self, ENNReal.ofReal_zero, Set.Ioc_eq_empty (not_lt.2 (hy.trans le_sup_right)),
      Measure.restrict_empty, lintegral_zero_measure]
  · have hy' : ((y.toNNReal : ℝ≥0) : ℝ) = y := Real.coe_toNNReal _ hy.le
    have hxn : ((x.toNNReal : ℝ≥0) : ℝ) = max x 0 := Real.coe_toNNReal' x
    have hle : x ⊔ 0 ≤ y := sup_le hxy.le hy.le
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((hφ.integrableOn_Icc (a := x ⊔ 0) (b := y)).mono_set Set.Ioc_subset_Icc_self) (ae_of_all _ hφ0),
      ← intervalIntegral.integral_of_le hle, hA, hA, hy', hxn]
    congr 1
    exact intervalIntegral.integral_interval_sub_left (hint 0 y) (hint 0 (x ⊔ 0))

/-- The Stieltjes measure of the approximating clock, restricted to `(0, 1]`, is `ρ_ε(b_s) ds`. -/
theorem restrict_stieltjesOfNNReal_measure_lqgClockApproxNN {γ ε : ℝ} (hε0 : 0 ≤ ε) {hε : ℝ → ℂ → ℝ}
    (hcont : Continuous (hε ε)) (b : ContinuousPath ℂ) :
    ((stieltjesOfNNReal fun t => lqgClockApproxNN γ hε ε t b).measure).restrict (Ioc (0 : ℝ) 1) =
      ((volume : Measure ℝ).restrict (Ioc 0 1)).withDensity fun s =>
        ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (b s.toNNReal))) := by
  rw [stieltjesOfNNReal_measure_lqgClockApproxNN hε0 hcont b,
    restrict_withDensity measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    Set.inter_eq_left.2 Set.Ioc_subset_Ioi_self]

/-- **The approximating Liouville clock is a positive continuous additive functional** of planar Brownian motion,
adapted to the natural filtration. -/
theorem isPCAF_lqgClockApproxNN {γ ε : ℝ} (hε0 : 0 ≤ ε) {hε : ℝ → ℂ → ℝ} (hcont : Continuous (hε ε)) :
    IsPCAF planarLaw (lqgClockApproxNN γ hε ε) := by
  have hGa : ∀ t, Measurable[pathFiltration t] (lqgClockApproxNN γ hε ε t) := fun t =>
    ((LQGClockApproxAdapted.measurable_lqgClockApprox_canonicalFiltration γ hcont.measurable t).mono
      (canonicalFiltration_le_pathFiltration t) le_rfl).real_toNNReal
  refine ⟨fun t => (hGa t).mono (pathFiltration_le_ambient t) le_rfl,
    fun z t => ⟨_, hGa t, Filter.EventuallyEq.rfl⟩, fun z => ae_of_all _ fun b => ?_,
    fun z s t => ae_of_all _ fun b => ?_⟩
  · refine ⟨?_, continuous_lqgClockApproxNN hcont b, monotone_lqgClockApproxNN hε0 hcont b⟩
    simp [lqgClockApproxNN, lqgClockApprox_zero]
  · rw [← NNReal.coe_inj, NNReal.coe_add, coe_lqgClockApproxNN hε0, coe_lqgClockApproxNN hε0,
      coe_lqgClockApproxNN hε0, lqgClockApprox_add_eq_add_shift hcont]
    have hs : LatticeProb.pathShift b t = ContinuousPath.shift t b := congrFun (pathShift_eq_shift t) b
    rw [hs]

/-- Under Lebesgue-started planar Brownian motion the position at a fixed time is Lebesgue distributed, in integral
form: `∫ dz E_z h(B_t) = ∫ h`. -/
theorem lintegral_lintegral_planarLaw_eval (t : ℝ≥0) {h : ℂ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ z, ∫⁻ ω, h (ω t) ∂planarLaw z = ∫⁻ x, h x := by
  have hm : Measurable fun ω : ContinuousPath ℂ => h (ω t) := hh.comp (continuous_eval_const t).measurable
  rw [← Measure.lintegral_bind measurable_planarLaw.aemeasurable hm.aemeasurable,
    ← lintegral_map hh (continuous_eval_const t).measurable, map_eval_bind_planarLaw]

theorem measurable_lintegral_planarLaw {X : Type*} [MeasurableSpace X] {p : X → ℂ} (hp : Measurable p)
    {f : X × ContinuousPath ℂ → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun x => ∫⁻ ω, f (x, ω) ∂planarLaw (p x) :=
  hf.lintegral_kernel_prod_right' (κ := ProbabilityTheory.Kernel.comap HarmonicBalls.planarBrownianMotion p hp)

/-- **The Revuz measure of the approximating Liouville clock** with respect to Lebesgue measure is the approximating
LQG measure `ε^{γ²/2} e^{γ h_ε(z)} dz`. -/
theorem revuz_lqgClockApproxNN {γ ε : ℝ} (hε0 : 0 ≤ ε) {hε : ℝ → ℂ → ℝ} (hcont : Continuous (hε ε)) :
    revuz planarLaw (lqgClockApproxNN γ hε ε) = LatticeProb.LQG.lqgApprox γ hε ε := by
  have hρ : Continuous fun x : ℂ => ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε x) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hcont))
  refine Measure.ext fun S hS => ?_
  set h : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε x)) * S.indicator 1 x with hh
  have hhm : Measurable h :=
    (ENNReal.measurable_ofReal.comp hρ.measurable).mul (measurable_one.indicator hS)
  have hev : Measurable fun p : ℝ × ContinuousPath ℂ => p.2 p.1.toNNReal :=
    (ContinuousEval.continuous_eval.comp
      ((continuous_snd).prodMk (continuous_real_toNNReal.comp continuous_fst))).measurable
  have h1 := lintegral_revuz_of_isPCAF measurable_planarLaw (isPCAF_lqgClockApproxNN (γ := γ) hε0 hcont)
    (g := S.indicator 1) (measurable_one.indicator hS)
  rw [lintegral_indicator_one hS] at h1
  rw [h1]
  have hω : ∀ ω : ContinuousPath ℂ, ∫⁻ s in Ioc (0 : ℝ) 1, S.indicator 1 (ω s.toNNReal)
      ∂(stieltjesOfNNReal fun t => lqgClockApproxNN γ hε ε t ω).measure =
        ∫⁻ s in Ioc (0 : ℝ) 1, h (ω s.toNNReal) := fun ω => by
    rw [restrict_stieltjesOfNNReal_measure_lqgClockApproxNN hε0 hcont ω]
    exact lintegral_withDensity_eq_lintegral_mul _
      (f := fun s : ℝ => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (ω s.toNNReal))))
      (ENNReal.measurable_ofReal.comp ((continuous_clockDensity hcont ω).measurable))
      (g := fun s : ℝ => S.indicator 1 (ω s.toNNReal))
      ((measurable_one.indicator hS).comp (ω.continuous.comp continuous_real_toNNReal).measurable)
  simp_rw [hω]
  have hjoint : Measurable fun p : ℝ × ContinuousPath ℂ => h (p.2 p.1.toNNReal) := hhm.comp hev
  have hswap : ∀ z : ℂ, ∫⁻ ω, (∫⁻ s in Ioc (0 : ℝ) 1, h (ω s.toNNReal)) ∂planarLaw z =
      ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ ω, h (ω s.toNNReal) ∂planarLaw z := fun z =>
    lintegral_lintegral_swap (hjoint.comp measurable_swap).aemeasurable
  simp_rw [hswap]
  have hmeasΦ : Measurable fun q : ℂ × ℝ => ∫⁻ ω, h (ω q.2.toNNReal) ∂planarLaw q.1 :=
    measurable_lintegral_planarLaw (p := Prod.fst) measurable_fst
      (f := fun r : (ℂ × ℝ) × ContinuousPath ℂ => h (r.2 r.1.2.toNNReal))
      (hhm.comp ((ContinuousEval.continuous_eval.comp
        ((continuous_snd).prodMk (continuous_real_toNNReal.comp (continuous_snd.comp continuous_fst)))).measurable))
  rw [lintegral_lintegral_swap hmeasΦ.aemeasurable]
  simp_rw [lintegral_lintegral_planarLaw_eval _ hhm]
  rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc,
    sub_zero, ENNReal.ofReal_one, mul_one]
  rw [LatticeProb.LQG.lqgApprox, withDensity_apply _ hS, ← lintegral_indicator hS]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ S <;> simp [hh, hx]

end MatedCRT.FirstPass.Derived
