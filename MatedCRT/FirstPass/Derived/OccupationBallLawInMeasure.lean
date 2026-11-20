import MatedCRT.FirstPass.Derived.LQGClockOccupationInMeasure
import MatedCRT.FirstPass.Derived.LQGApproxWindowSecondMoment

/-!
# Convergence in measure of the occupation integrals under the path law averaged over a disc

Let `ballLaw R = ∫_{B(0, R)} planarLaw z dz`, the path law of planar Brownian motion started from
Lebesgue measure restricted to the disc `B(0, R)`; it is a finite measure on `C([0, ∞), ℂ)`.

* `integral_occupationMeasure_lqgClockApproxNN`: the occupation integral `∫ f d(occupation measure of
  the approximating Liouville clock)` is the window occupation integral `∫_{(0,1]} f ρ_ε (b_s) ds`;
* `tendstoInMeasure_ballLaw_of_forall`: convergence in `planarLaw z`-measure for every start `z` gives
  convergence in `ballLaw R`-measure (dominated convergence in `z`);
* `exists_measurable_version_integral_occupationMeasure`: the occupation integral of a PCAF has a
  measurable version, common to all starts;
* `exists_measurable_tendstoInMeasure_ballLaw_lqgClock`: the occupation integrals of the approximating
  Liouville clocks converge in `ballLaw R`-measure to a measurable version of the occupation integral
  of the limiting clock.
-/

open MeasureTheory MarkovProcess Set Filter Topology Metric
open HarmonicBalls (lqgClockApprox IsLQGClock planarBrownianMotion)
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

instance isProbabilityMeasure_planarLaw' (z : ℂ) : IsProbabilityMeasure (planarLaw z) := by
  unfold planarLaw; infer_instance

/-- The path law of planar Brownian motion started from Lebesgue measure restricted to `B(0, R)`:
`ballLaw R = ∫_{B(0, R)} planarLaw z dz`. -/
noncomputable def ballLaw (R : ℝ) : Measure (ContinuousPath ℂ) :=
  ((volume : Measure ℂ).restrict (ball (0 : ℂ) R)).bind planarLaw

theorem ballLaw_apply (R : ℝ) {S : Set (ContinuousPath ℂ)} (hS : MeasurableSet S) :
    ballLaw R S = ∫⁻ z in ball (0 : ℂ) R, planarLaw z S :=
  Measure.bind_apply hS measurable_planarLaw.aemeasurable

instance isFiniteMeasure_ballLaw (R : ℝ) : IsFiniteMeasure (ballLaw R) :=
  ⟨by
    rw [ballLaw_apply R MeasurableSet.univ]
    simp only [measure_univ, lintegral_const, one_mul, Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩

/-- **Convergence in measure from every start gives convergence in measure under the disc law**
(dominated convergence in the starting point). -/
theorem tendstoInMeasure_ballLaw_of_forall (R : ℝ) {X : ℕ → ContinuousPath ℂ → ℝ}
    {Φ : ContinuousPath ℂ → ℝ} (hX : ∀ k, Measurable (X k)) (hΦ : Measurable Φ)
    (h : ∀ z, TendstoInMeasure (planarLaw z) X atTop Φ) :
    TendstoInMeasure (ballLaw R) X atTop Φ := by
  intro ε hε
  have hS : ∀ k, MeasurableSet {b | ε ≤ edist (X k b) (Φ b)} := fun k =>
    measurableSet_le measurable_const ((hX k).edist hΦ)
  simp_rw [ballLaw_apply R (hS _)]
  have := tendsto_lintegral_of_dominated_convergence (μ := (volume : Measure ℂ).restrict (ball (0 : ℂ) R))
    (F := fun k z => planarLaw z {b | ε ≤ edist (X k b) (Φ b)}) (f := fun _ => 0)
    (fun _ => 1) (fun k => (Measure.measurable_coe (hS k)).comp measurable_planarLaw)
    (fun k => ae_of_all _ fun z => prob_le_one)
    (by simp only [lintegral_const, one_mul, Measure.restrict_apply_univ]
        exact measure_ball_lt_top.ne)
    (ae_of_all _ fun z => h z ε hε)
  simpa using this

/-- The occupation integral of a PCAF against a continuous nonnegative function has a measurable
version `Φ`, the same for every start. -/
theorem exists_measurable_version_integral_occupationMeasure
    {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF planarLaw A) {f : ℂ → ℝ} (hf : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x) :
    ∃ Φ : ContinuousPath ℂ → ℝ, Measurable Φ ∧ ∀ z,
      (fun b => ∫ x, f x ∂occupationMeasure (fun t => A t b) b) =ᵐ[planarLaw z] Φ := by
  have hg : Measurable fun x => ENNReal.ofReal (f x) :=
    ENNReal.measurable_ofReal.comp hf.measurable
  have hΦ : Measurable fun b : ContinuousPath ℂ =>
      ∫⁻ y, ENNReal.ofReal (f y) ∂occupationMeasure (fun u => regularize A u b) b :=
    (Measure.measurable_lintegral hg).comp (measurable_occupationMeasure_regularize hA.meas)
  refine ⟨_, hΦ.ennreal_toReal, fun z => EventuallyEq.symm ?_⟩
  filter_upwards [hA.path z] with b hb
  show ENNReal.toReal _ = _
  rw [occupationMeasure_regularize_eq_of_path hb.2.1 hb.2.2,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hf.aestronglyMeasurable]

/-- **The occupation integral of the approximating Liouville clock is a window occupation
integral**: `∫ f d(occupation measure of t ↦ ∫_0^t ρ_ε(b_u) du) = ∫_{(0,1]} f(b_s) ρ_ε(b_s) ds`. -/
theorem integral_occupationMeasure_lqgClockApproxNN {γ ε : ℝ} (hε0 : 0 ≤ ε) {hε : ℝ → ℂ → ℝ}
    (hcont : Continuous (hε ε)) (b : ContinuousPath ℂ) {f : ℂ → ℝ} (hf : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x) :
    ∫ x, f x ∂occupationMeasure (fun t => lqgClockApproxNN γ hε ε t b) b =
      (windowOcc (fun x => ENNReal.ofReal (f x) *
        ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε x))) b).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hf.aestronglyMeasurable]
  congr 1
  have hev : Measurable fun s : ℝ => b s.toNNReal :=
    (b.continuous.comp continuous_real_toNNReal).measurable
  have hfm : Measurable fun x => ENNReal.ofReal (f x) := ENNReal.measurable_ofReal.comp hf.measurable
  have hw := lintegral_withDensity_eq_lintegral_mul ((volume : Measure ℝ).restrict (Ioc 0 1))
    (f := fun s : ℝ => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (b s.toNNReal))))
    (ENNReal.measurable_ofReal.comp (continuous_clockDensity hcont b).measurable)
    (g := fun s : ℝ => ENNReal.ofReal (f (b s.toNNReal))) (hfm.comp hev)
  unfold occupationMeasure windowOcc
  rw [lintegral_map hfm hev, restrict_stieltjesOfNNReal_measure_lqgClockApproxNN hε0 hcont b]
  refine hw.trans (setLIntegral_congr_fun measurableSet_Ioc fun s _ => ?_)
  simp only [Pi.mul_apply]
  exact mul_comm _ _

theorem dyadicScale_eq (k : ℕ) :
    HarmonicBalls.dyadicScale k = LatticeProb.LQG.dyadicScale k := rfl

/-- **Convergence in measure of the occupation integrals under the disc law.**  If for every start `z`
the approximating clocks converge to the clock `G` in the sense of `IsLQGClock`, then the occupation
integrals `X_k` of the approximating clocks converge in `ballLaw R`-measure to a measurable version
`Φ` of the occupation integral of `G`, which is the `planarLaw z`-a.s. limit version for every `z`. -/
theorem exists_measurable_tendstoInMeasure_ballLaw_lqgClock {γ : ℝ} {hE : ℝ → ℂ → ℝ}
    (hcont : ∀ k : ℕ, Continuous (hE (HarmonicBalls.dyadicScale k)))
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (hF : ∀ z, IsLQGClock planarBrownianMotion γ hE z F)
    {G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hG : IsPCAF planarLaw G)
    (hGF : ∀ z, ∀ᵐ b ∂planarLaw z, ∀ t, (G t b : ℝ) = F b t)
    {f : ℂ → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) (R : ℝ) :
    ∃ Φ : ContinuousPath ℂ → ℝ, Measurable Φ ∧
      (∀ z, (fun b => ∫ x, f x ∂occupationMeasure (fun t => G t b) b) =ᵐ[planarLaw z] Φ) ∧
      TendstoInMeasure (ballLaw R)
        (fun k b => ∫ x, f x ∂occupationMeasure
          (fun t => lqgClockApproxNN γ hE (HarmonicBalls.dyadicScale k) t b) b) atTop Φ := by
  obtain ⟨Φ, hΦ, hver⟩ := exists_measurable_version_integral_occupationMeasure hG hf hf0
  refine ⟨Φ, hΦ, hver, tendstoInMeasure_ballLaw_of_forall R (fun k => ?_) hΦ fun z => ?_⟩
  · have hε0 := (HarmonicBalls.dyadicScale_pos k).le
    have hm : Measurable (weightedApproxDensity γ hE f k) :=
      measurable_weightedApproxDensity hf.measurable (hcont k).measurable
    show Measurable fun b : ContinuousPath ℂ => ∫ x, f x ∂occupationMeasure
      (fun t => lqgClockApproxNN γ hE (HarmonicBalls.dyadicScale k) t b) b
    have e : (fun b : ContinuousPath ℂ => ∫ x, f x ∂occupationMeasure
        (fun t => lqgClockApproxNN γ hE (HarmonicBalls.dyadicScale k) t b) b) =
        fun b => (windowOcc (weightedApproxDensity γ hE f k) b).toReal :=
      funext fun b => integral_occupationMeasure_lqgClockApproxNN hε0 (hcont k) b hf hf0
    rw [e]
    exact (measurable_windowOcc hm).ennreal_toReal
  · exact (tendstoInMeasure_integral_occupationMeasure_lqgClock hcont z (hF z) hG (hGF z) hf hf0).congr_right
      (hver z)

end MatedCRT.FirstPass.Derived
