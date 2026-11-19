import MatedCRT.FirstPass.Derived.RevuzPositive
import LatticeProb.Analysis.UniformLimitWeightedSetIntegrals

/-!
# Integrals against uniformly convergent continuous clocks

Let `a k, a : ℝ≥0 → ℝ≥0` be continuous nondecreasing clocks with `a k → a` uniformly on `[0, 1]`. For every `g`
continuous on `[0, 1]`, the Lebesgue–Stieltjes integrals converge:
`∫_{(0,t]} g d(a k) → ∫_{(0,t]} g da`, uniformly in `t ∈ [0, 1]`.

* `tendstoUniformlyOn_setIntegral_Ioc_stieltjesOfNNReal`: the uniform form;
* `tendsto_setIntegral_Ioc_stieltjesOfNNReal`: the window `(0, 1]`;
* `tendsto_integral_occupationMeasure_of_tendstoUniformlyOn`: for a continuous path `ω` and a continuous
  `f : ℂ → ℝ`, `∫ f d(occupationMeasure (a k) ω) → ∫ f d(occupationMeasure a ω)`, i.e.
  `∫_{(0,1]} f(ω_s) d(a k)_s → ∫_{(0,1]} f(ω_s) da_s`.

The proof restricts the Stieltjes measures to `(0, 1]`, where they are finite with distribution functions
`t ↦ a t - a 0`, and applies the convergence of integrals against uniformly convergent distribution functions
(`LatticeProb.tendstoUniformlyOn_setIntegral_Ioc_of_measureReal`).
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess

/-- The Stieltjes measure of a continuous nondecreasing clock, restricted to a bounded interval `(x, y]`, is
finite. -/
theorem isFiniteMeasure_stieltjesOfNNReal_restrict_Ioc {a : ℝ≥0 → ℝ≥0} (hm : Monotone a) (hc : Continuous a)
    (x y : ℝ) : IsFiniteMeasure (((stieltjesOfNNReal a).measure).restrict (Ioc x y)) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ, stieltjesOfNNReal_measure_Ioc hm hc]
  exact ENNReal.ofReal_lt_top

/-- The distribution function of the Stieltjes measure of a continuous nondecreasing clock restricted to
`(0, 1]`: for `t ∈ [0, 1]`, the mass of `(0, t]` is `a t - a 0`. -/
theorem measureReal_stieltjesOfNNReal_restrict_Ioc {a : ℝ≥0 → ℝ≥0} (hm : Monotone a) (hc : Continuous a)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (((stieltjesOfNNReal a).measure).restrict (Ioc 0 1)).real (Ioc 0 t) = (a t.toNNReal : ℝ) - a 0 := by
  rw [measureReal_def, Measure.restrict_apply measurableSet_Ioc,
    inter_eq_left.2 (Ioc_subset_Ioc le_rfl ht.2), stieltjesOfNNReal_measure_Ioc hm hc, Real.toNNReal_zero,
    ENNReal.toReal_ofReal (sub_nonneg.2 (NNReal.coe_le_coe.2 (hm (zero_le))))]

/-- **Uniform convergence of Lebesgue–Stieltjes integrals.** If continuous nondecreasing clocks `a k` converge to a
continuous nondecreasing clock `a` uniformly on `[0, 1]`, then for every `g` continuous on `[0, 1]`,
`∫_{(0,t]} g d(a k) → ∫_{(0,t]} g da` uniformly in `t ∈ [0, 1]`. -/
theorem tendstoUniformlyOn_setIntegral_Ioc_stieltjesOfNNReal {a : ℕ → ℝ≥0 → ℝ≥0} {a' : ℝ≥0 → ℝ≥0}
    (ham : ∀ k, Monotone (a k)) (hac : ∀ k, Continuous (a k)) (hm : Monotone a') (hc : Continuous a')
    (hu : TendstoUniformlyOn (fun k t => (a k t : ℝ)) (fun t => (a' t : ℝ)) atTop (Icc 0 1))
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 1)) :
    TendstoUniformlyOn (fun k t => ∫ s in Ioc 0 t, g s ∂(stieltjesOfNNReal (a k)).measure)
      (fun t => ∫ s in Ioc 0 t, g s ∂(stieltjesOfNNReal a').measure) atTop (Icc 0 1) := by
  have : ∀ k, IsFiniteMeasure (((stieltjesOfNNReal (a k)).measure).restrict (Ioc 0 1)) := fun k =>
    isFiniteMeasure_stieltjesOfNNReal_restrict_Ioc (ham k) (hac k) 0 1
  have : IsFiniteMeasure (((stieltjesOfNNReal a').measure).restrict (Ioc 0 1)) :=
    isFiniteMeasure_stieltjesOfNNReal_restrict_Ioc hm hc 0 1
  -- the distribution functions on `(0, 1]` converge uniformly on `[0, 1]`
  have hcdf : TendstoUniformlyOn
      (fun k t => (((stieltjesOfNNReal (a k)).measure).restrict (Ioc 0 1)).real (Ioc 0 t))
      (fun t => (((stieltjesOfNNReal a').measure).restrict (Ioc 0 1)).real (Ioc 0 t)) atTop (Icc 0 1) := by
    rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
    intro ε hε
    filter_upwards [hu (ε / 2) (half_pos hε)] with k hk t ht
    have h0 : (0 : ℝ≥0) ∈ Icc (0 : ℝ≥0) 1 := ⟨le_rfl, zero_le_one⟩
    have h1 : t.toNNReal ∈ Icc (0 : ℝ≥0) 1 :=
      ⟨zero_le, by simpa using Real.toNNReal_le_toNNReal ht.2⟩
    have ht' := hk _ h1
    have h0' := hk _ h0
    rw [measureReal_stieltjesOfNNReal_restrict_Ioc (ham k) (hac k) ht,
      measureReal_stieltjesOfNNReal_restrict_Ioc hm hc ht]
    rw [Real.dist_eq] at ht' h0' ⊢
    calc |((a' t.toNNReal : ℝ) - a' 0) - ((a k t.toNNReal : ℝ) - a k 0)|
        = |((a' t.toNNReal : ℝ) - a k t.toNNReal) - ((a' 0 : ℝ) - a k 0)| := by congr 1; ring
      _ ≤ |(a' t.toNNReal : ℝ) - a k t.toNNReal| + |(a' 0 : ℝ) - a k 0| := abs_sub _ _
      _ < ε / 2 + ε / 2 := add_lt_add ht' h0'
      _ = ε := add_halves ε
  have key := LatticeProb.tendstoUniformlyOn_setIntegral_Ioc_of_measureReal hcdf hg
  -- on `[0, 1]`, restricting to `(0, 1]` does not change the integrals over `(0, t]`
  have hrestr : ∀ (m : Measure ℝ) {t : ℝ}, t ∈ Icc (0 : ℝ) 1 →
      ∫ s in Ioc 0 t, g s ∂(m.restrict (Ioc 0 1)) = ∫ s in Ioc 0 t, g s ∂m := by
    intro m t ht
    rw [Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.2 (Ioc_subset_Ioc le_rfl ht.2)]
  refine (key.congr (Eventually.of_forall fun k t ht => hrestr _ ht)).congr_right
    (fun t ht => hrestr _ ht)

/-- **Convergence of Lebesgue–Stieltjes integrals on `(0, 1]`.** If continuous nondecreasing clocks `a k` converge
to a continuous nondecreasing clock `a` uniformly on `[0, 1]`, then `∫_{(0,1]} g d(a k) → ∫_{(0,1]} g da` for
every `g` continuous on `[0, 1]`. -/
theorem tendsto_setIntegral_Ioc_stieltjesOfNNReal {a : ℕ → ℝ≥0 → ℝ≥0} {a' : ℝ≥0 → ℝ≥0}
    (ham : ∀ k, Monotone (a k)) (hac : ∀ k, Continuous (a k)) (hm : Monotone a') (hc : Continuous a')
    (hu : TendstoUniformlyOn (fun k t => (a k t : ℝ)) (fun t => (a' t : ℝ)) atTop (Icc 0 1))
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 1)) :
    Tendsto (fun k => ∫ s in Ioc 0 1, g s ∂(stieltjesOfNNReal (a k)).measure) atTop
      (𝓝 (∫ s in Ioc 0 1, g s ∂(stieltjesOfNNReal a').measure)) :=
  (tendstoUniformlyOn_setIntegral_Ioc_stieltjesOfNNReal ham hac hm hc hu hg).tendsto_at
    ⟨zero_le_one, le_rfl⟩

/-- The integral of a continuous function against the occupation measure of a continuous path is the
Lebesgue–Stieltjes integral `∫_{(0,1]} f(ω_s) da_s`. -/
theorem integral_occupationMeasure {a : ℝ≥0 → ℝ≥0} (ω : ContinuousPath ℂ) {f : ℂ → ℝ} (hf : Continuous f) :
    ∫ x, f x ∂occupationMeasure a ω = ∫ s in Ioc 0 1, f (ω s.toNNReal) ∂(stieltjesOfNNReal a).measure := by
  rw [occupationMeasure]
  exact integral_map (φ := fun s : ℝ => ω s.toNNReal)
    (ω.continuous.comp continuous_real_toNNReal).measurable.aemeasurable hf.aestronglyMeasurable

/-- **Occupation integrals along a path converge under uniform convergence of the clocks.** If continuous
nondecreasing clocks `a k` converge to a continuous nondecreasing clock `a` uniformly on `[0, 1]`, then for every
continuous path `ω` and continuous `f : ℂ → ℝ`, `∫ f d(occupationMeasure (a k) ω) → ∫ f d(occupationMeasure a ω)`. -/
theorem tendsto_integral_occupationMeasure_of_tendstoUniformlyOn {a : ℕ → ℝ≥0 → ℝ≥0} {a' : ℝ≥0 → ℝ≥0}
    (ham : ∀ k, Monotone (a k)) (hac : ∀ k, Continuous (a k)) (hm : Monotone a') (hc : Continuous a')
    (hu : TendstoUniformlyOn (fun k t => (a k t : ℝ)) (fun t => (a' t : ℝ)) atTop (Icc 0 1))
    (ω : ContinuousPath ℂ) {f : ℂ → ℝ} (hf : Continuous f) :
    Tendsto (fun k => ∫ x, f x ∂occupationMeasure (a k) ω) atTop
      (𝓝 (∫ x, f x ∂occupationMeasure a' ω)) := by
  simp only [integral_occupationMeasure ω hf]
  exact tendsto_setIntegral_Ioc_stieltjesOfNNReal ham hac hm hc hu
    (hf.comp (ω.continuous.comp continuous_real_toNNReal)).continuousOn

end MatedCRT
