import HarmonicBalls.Proofs.Potential.FiniteDiscGreenReciprocity
import HarmonicBalls.Proofs.Sec6.AvoidanceBallSubmean

/-!
# Bounded measurable functions with the circle mean-value property are harmonic

Let `f : ℂ → ℝ` be bounded and measurable, and suppose `f x` equals the circle average of `f` on
every circle `∂B(x, r)` whose closed disc lies in an open set `V`.  Integrating the circle averages
in polar coordinates gives the area mean-value property `∫_{B(x, r)} f = π r² f x`.  Writing
`f x'` as the area average over `B(x', r)` for `x'` near `x`, continuity of `x' ↦ ∫_{B(x', r)} f`
(dominated convergence, the sphere `∂B(x, r)` being null) shows that `f` is continuous on `V`.
A continuous function with the circle mean-value property is harmonic.
-/

set_option autoImplicit false

namespace MatedCRT.BrownianBeurling

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

private lemma integrableOn_comp_circleMap {f : ℂ → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ z, |f z| ≤ M) (c : ℂ) (r : ℝ) {a b : ℝ} :
    IntegrableOn (fun θ => f (circleMap c r θ)) (Ioc a b) := by
  refine Measure.integrableOn_of_bounded (M := M) (by simp) ?_ ?_
  · exact (hf.comp (continuous_circleMap c r).measurable).aestronglyMeasurable
  · exact Eventually.of_forall fun θ => by simpa only [Real.norm_eq_abs] using hM _

private lemma circleIntegrable_of_bounded {f : ℂ → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ z, |f z| ≤ M) (c : ℂ) (r : ℝ) : CircleIntegrable f c r := by
  have h := integrableOn_comp_circleMap hf hM c r (a := 0) (b := 2 * Real.pi)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).2 h

private lemma lintegral_circle_shift {f : ℂ → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ z, |f z| ≤ M) {x : ℂ} {s : ℝ}
    (hmean : Real.circleAverage f x s = f x) :
    ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (f (circleMap x s θ) + M) =
      ENNReal.ofReal (2 * Real.pi * (f x + M)) := by
  have hint : IntegrableOn (fun θ => f (circleMap x s θ) + M) (Ioo (-Real.pi) Real.pi) :=
    ((integrableOn_comp_circleMap hf hM x s (a := -Real.pi) (b := Real.pi)).mono_set
      Ioo_subset_Ioc_self).add (integrableOn_const (by simp))
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (-Real.pi) Real.pi)]
      fun θ => f (circleMap x s θ) + M :=
    Eventually.of_forall fun θ => by
      have := abs_le.mp (hM (circleMap x s θ))
      simp only [Pi.zero_apply]
      linarith [this.1]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  have hp : Function.Periodic (fun θ => f (circleMap x s θ) + M) (2 * Real.pi) := fun θ => by
    simp only [(periodic_circleMap x s) θ]
  have hci := circleIntegrable_of_bounded hf hM x s
  calc ∫ θ in Ioo (-Real.pi) Real.pi, (f (circleMap x s θ) + M)
      = ∫ θ in (-Real.pi)..(-Real.pi + 2 * Real.pi), (f (circleMap x s θ) + M) := by
        rw [show -Real.pi + 2 * Real.pi = Real.pi by ring,
          intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
          integral_Ioc_eq_integral_Ioo]
    _ = ∫ θ in (0 : ℝ)..(0 + 2 * Real.pi), (f (circleMap x s θ) + M) :=
        hp.intervalIntegral_add_eq _ _
    _ = 2 * Real.pi * (f x + M) := by
        rw [zero_add, intervalIntegral.integral_add hci intervalIntegrable_const]
        have h2 : ∫ θ in (0 : ℝ)..2 * Real.pi, f (circleMap x s θ) = 2 * Real.pi * f x := by
          have := hmean
          rw [Real.circleAverage_def, smul_eq_mul] at this
          field_simp at this
          linarith
        rw [h2]
        simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
        ring

private lemma setIntegral_ball_eq_of_circleAverage {f : ℂ → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ z, |f z| ≤ M) {x : ℂ} {r : ℝ} (hr : 0 < r)
    (hmean : ∀ s ∈ Ioo 0 r, Real.circleAverage f x s = f x) :
    ∫ y in ball x r, f y = Real.pi * r ^ 2 * f x := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hfM : ∀ y, 0 ≤ f y + M := fun y => by linarith [(abs_le.mp (hM y)).1]
  have hK : 0 ≤ 2 * Real.pi * (f x + M) := by have := hfM x; positivity
  have hg : Measurable fun y => ENNReal.ofReal (f y + M) := (hf.add_const M).ennreal_ofReal
  have h1 : ∫⁻ y in ball x r, ENNReal.ofReal (f y + M) =
      ENNReal.ofReal (Real.pi * r ^ 2 * (f x + M)) := by
    rw [HarmonicBalls.Section6.lintegral_ball_polar x r hg]
    have hin : ∀ s ∈ Ioo (0 : ℝ) r, ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal s * ENNReal.ofReal (f (circleMap x s θ) + M) =
        ENNReal.ofReal (s * (2 * Real.pi * (f x + M))) := by
      intro s hs
      have hm : Measurable fun θ : ℝ => ENNReal.ofReal (f (circleMap x s θ) + M) :=
        hg.comp (continuous_circleMap x s).measurable
      rw [lintegral_const_mul _ hm,
        lintegral_circle_shift hf hM (hmean s hs), ← ENNReal.ofReal_mul hs.1.le]
    rw [setLIntegral_congr_fun measurableSet_Ioo hin]
    have hint : IntegrableOn (fun s : ℝ => s * (2 * Real.pi * (f x + M))) (Ioo 0 r) :=
      ((continuous_id.mul continuous_const).integrableOn_Icc).mono_set Ioo_subset_Icc_self
    have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) r)]
        fun s : ℝ => s * (2 * Real.pi * (f x + M)) :=
      (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun s hs => by
        simp only [Pi.zero_apply]
        exact mul_nonneg hs.1.le hK)
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
    congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le,
      intervalIntegral.integral_mul_const, integral_id]
    ring
  have hfi : IntegrableOn f (ball x r) :=
    Measure.integrableOn_of_bounded (M := M) measure_ball_lt_top.ne hf.aestronglyMeasurable
      (Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hM y)
  have h2 : ∫ y in ball x r, (f y + M) = Real.pi * r ^ 2 * (f x + M) := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hfM)
      (hf.add_const M).aestronglyMeasurable, h1, ENNReal.toReal_ofReal]
    have := hfM x
    positivity
  rw [integral_add hfi (integrableOn_const measure_ball_lt_top.ne), setIntegral_const,
    measureReal_def, Complex.volume_ball] at h2
  have hv : (ENNReal.ofReal r ^ 2 * (NNReal.pi : ℝ≥0∞)).toReal = r ^ 2 * Real.pi := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr.le]
    simp
  rw [hv, smul_eq_mul] at h2
  linarith

private lemma continuousAt_setIntegral_ball {f : ℂ → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ z, |f z| ≤ M) (x : ℂ) {r : ℝ} (hr : 0 < r) :
    ContinuousAt (fun x' => ∫ y in ball x' r, f y) x := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hfun : (fun x' => ∫ y in ball x' r, f y) =
      fun x' => ∫ y, (ball x' r).indicator f y := funext fun x' =>
    (integral_indicator measurableSet_ball).symm
  rw [hfun]
  refine continuousAt_of_dominated (bound := (ball x (2 * r)).indicator fun _ => M) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun x' =>
      (hf.indicator measurableSet_ball).aestronglyMeasurable
  · filter_upwards [ball_mem_nhds x hr] with x' hx'
    refine Eventually.of_forall fun y => ?_
    by_cases hy : y ∈ ball x' r
    · have hy2 : y ∈ ball x (2 * r) := by
        rw [mem_ball] at hx' hy ⊢
        linarith [dist_triangle y x' x]
      rw [indicator_of_mem hy, indicator_of_mem hy2]
      simpa only [Real.norm_eq_abs] using hM y
    · rw [indicator_of_notMem hy, norm_zero]
      exact indicator_nonneg (fun _ _ => hM0) y
  · exact (integrable_indicator_iff measurableSet_ball).2
      (integrableOn_const measure_ball_lt_top.ne)
  · have hnull : ∀ᵐ y : ℂ, y ∉ sphere x r :=
      measure_eq_zero_iff_ae_notMem.1 (Measure.addHaar_sphere volume x r)
    filter_upwards [hnull] with y hy
    have hd : dist y x ≠ r := hy
    rcases lt_or_gt_of_ne hd with h | h
    · have hev : ∀ᶠ x' in 𝓝 x, y ∈ ball x' r := by
        have : ∀ᶠ x' in 𝓝 x, dist y x' < r :=
          ContinuousAt.eventually_lt (f := fun x' => dist y x') (g := fun _ => r)
            (by fun_prop) continuousAt_const h
        filter_upwards [this] with x' hx'
        simpa only [mem_ball] using hx'
      refine (continuousAt_const (y := f y)).congr ?_
      filter_upwards [hev] with x' hx'
      rw [indicator_of_mem hx']
    · have hev : ∀ᶠ x' in 𝓝 x, y ∉ ball x' r := by
        have : ∀ᶠ x' in 𝓝 x, r < dist y x' :=
          ContinuousAt.eventually_lt (f := fun _ => r) (g := fun x' => dist y x')
            continuousAt_const (by fun_prop) h
        filter_upwards [this] with x' hx'
        simpa only [mem_ball, not_lt] using hx'.le
      refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [hev] with x' hx'
      rw [indicator_of_notMem hx']

/-- A bounded measurable function with the circle mean-value property on an open set is
continuous there. -/
theorem continuousOn_of_forall_circleAverage_eq {V : Set ℂ} (hV : IsOpen V) {f : ℂ → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M)
    (hmean : ∀ x ∈ V, ∀ r : ℝ, 0 < r → closedBall x r ⊆ V →
      Real.circleAverage f x r = f x) :
    ContinuousOn f V := by
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hV x hx
  set r : ℝ := ε / 4 with hr_def
  have hr : 0 < r := by positivity
  have hcont := (continuousAt_setIntegral_ball hf hM x hr).const_smul (Real.pi * r ^ 2)⁻¹
  refine hcont.congr ?_
  filter_upwards [ball_mem_nhds x hr] with x' hx'
  have hsub : closedBall x' r ⊆ V := by
    intro y hy
    apply hεV
    rw [mem_ball]
    rw [mem_closedBall] at hy
    rw [mem_ball] at hx'
    linarith [dist_triangle y x' x]
  have hx'V : x' ∈ V := hsub (mem_closedBall_self hr.le)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [setIntegral_ball_eq_of_circleAverage hf hM hr fun s hs =>
    hmean x' hx'V s hs.1 ((closedBall_subset_closedBall hs.2.le).trans hsub)]
  have : Real.pi * r ^ 2 ≠ 0 := by positivity
  field_simp

/-- A bounded measurable function with the circle mean-value property on an open set is
harmonic there. -/
theorem harmonicOnNhd_of_forall_circleAverage_eq {V : Set ℂ} (hV : IsOpen V) {f : ℂ → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M)
    (hmean : ∀ x ∈ V, ∀ r : ℝ, 0 < r → closedBall x r ⊆ V →
      Real.circleAverage f x r = f x) :
    InnerProductSpace.HarmonicOnNhd f V :=
  HarmonicBalls.harmonicOnNhd_of_circleAverage_eq hV
    (continuousOn_of_forall_circleAverage_eq hV hf hM hmean) hmean

end MatedCRT.BrownianBeurling
