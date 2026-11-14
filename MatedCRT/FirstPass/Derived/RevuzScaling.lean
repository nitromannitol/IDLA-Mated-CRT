import MatedCRT.FirstPass.Derived.RevuzFormula

/-!
# Scaling of a clock and of its Revuz measure

For a constant `c ≠ 0` the clock `c A` has the Revuz measure `c · revuz A`:

* the rational-time regularization is homogeneous (`regularize_const_mul`);
* the Lebesgue–Stieltjes measure and the occupation measure of a clock scale linearly
  (`stieltjesOfNNReal_measure_const_mul`, `occupationMeasure_const_mul`);
* integrating a kernel multiplied by a constant multiplies the integral (`bind_const_smul_kernel`);
* hence `revuz W (c A) = c • revuz W A` (`revuz_const_mul`).

A positive continuous additive functional multiplied by a constant is again one (`IsPCAF.const_mul`), and the clock
`c A` is good for `c ≠ 0` when `A` is (`GoodClock.const_mul`).

A locally finite measure on the plane is `σ`-finite by the Mathlib instance `sigmaFinite_of_locallyFinite`.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess

/-- The rational-time regularization is homogeneous in the clock. -/
theorem regularize_const_mul {c : ℝ≥0} (hc : c ≠ 0) (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (t : ℝ≥0)
    (ω : ContinuousPath ℂ) :
    regularize (fun s ω' => c * A s ω') t ω = c * regularize A t ω := by
  have hne := nonempty_regularize_index t
  have hcpos : 0 < c := pos_iff_ne_zero.2 hc
  unfold regularize
  beta_reduce
  have hiff : (∀ p q : ℚ≥0, p ≤ q → c * A p ω ≤ c * A q ω) ↔ ∀ p q : ℚ≥0, p ≤ q → A p ω ≤ A q ω :=
    forall_congr' fun p => forall_congr' fun q => imp_congr_right fun _ =>
      (OrderIso.mulLeft₀ c hcpos).le_iff_le (x := A p ω) (y := A q ω)
  by_cases h : ∀ p q : ℚ≥0, p ≤ q → A p ω ≤ A q ω
  · have h1 := hiff.2 h
    split_ifs
    exact ((OrderIso.mulLeft₀ c hcpos).map_ciInf (OrderBot.bddBelow _)).symm
  · have h1 := mt hiff.1 h
    split_ifs
    simp

/-- The right limit of a nonnegative multiple of a monotone function is the multiple of the right limit. -/
theorem rightLim_const_mul {f : ℝ → ℝ} (hf : Monotone f) {c : ℝ} (hc : 0 ≤ c) (x : ℝ) :
    Function.rightLim (fun y => c * f y) x = c * Function.rightLim f x := by
  have hg : Monotone (fun y => c * f y) := fun a b h => mul_le_mul_of_nonneg_left (hf h) hc
  exact tendsto_nhds_unique (hg.tendsto_rightLim x) ((hf.tendsto_rightLim x).const_mul c)

/-- The Lebesgue–Stieltjes measure of a clock scales with the clock. -/
theorem stieltjesOfNNReal_measure_const_mul {c : ℝ≥0} (hc : c ≠ 0) (a : ℝ≥0 → ℝ≥0) :
    (stieltjesOfNNReal fun t => c * a t).measure = (c : ℝ≥0∞) • (stieltjesOfNNReal a).measure := by
  by_cases h : Monotone a
  · have h' : Monotone fun t => c * a t := fun s t hst => mul_le_mul_of_nonneg_left (h hst) (by positivity)
    have hf : Monotone (fun x : ℝ => ((a x.toNNReal : ℝ≥0) : ℝ)) :=
      fun x y hxy => by exact_mod_cast h (Real.toNNReal_mono hxy)
    unfold stieltjesOfNNReal
    simp only [h, h', ↓reduceDIte]
    refine Measure.ext_of_Ioc' _ _
      (fun x y _ => by rw [StieltjesFunction.measure_Ioc]; exact ENNReal.ofReal_ne_top) fun x y _ => ?_
    rw [StieltjesFunction.measure_Ioc, Measure.smul_apply, StieltjesFunction.measure_Ioc, smul_eq_mul,
      Monotone.stieltjesFunction_eq, Monotone.stieltjesFunction_eq, Monotone.stieltjesFunction_eq,
      Monotone.stieltjesFunction_eq]
    simp only [NNReal.coe_mul]
    rw [rightLim_const_mul hf c.coe_nonneg, rightLim_const_mul hf c.coe_nonneg, ← mul_sub,
      ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  · have h' : ¬ Monotone fun t => c * a t := fun hm => h fun s t hst => by
      have := hm hst
      exact (OrderIso.mulLeft₀ c (pos_iff_ne_zero.2 hc)).le_iff_le.1 this
    unfold stieltjesOfNNReal
    simp only [h, h', ↓reduceDIte]
    have hd : (default : StieltjesFunction ℝ).measure = 0 := StieltjesFunction.measure_const 0
    rw [hd, smul_zero]

/-- The occupation measure of a clock scales with the clock. -/
theorem occupationMeasure_const_mul {c : ℝ≥0} (hc : c ≠ 0) (a : ℝ≥0 → ℝ≥0) (ω : ContinuousPath ℂ) :
    occupationMeasure (fun t => c * a t) ω = (c : ℝ≥0∞) • occupationMeasure a ω := by
  have hmeas : Measurable (fun s : ℝ => ω s.toNNReal) :=
    (ω.continuous.comp continuous_real_toNNReal).measurable
  unfold occupationMeasure
  rw [stieltjesOfNNReal_measure_const_mul hc, Measure.restrict_smul, Measure.map_smul _ hmeas.aemeasurable]

/-- Multiplying a measure by a constant is measurable on the space of measures. -/
theorem measurable_const_smul_measure {β : Type*} [MeasurableSpace β] (c : ℝ≥0∞) :
    Measurable (fun μ : Measure β => c • μ) :=
  Measure.measurable_of_measurable_coe _ fun s hs => by
    simp only [Measure.smul_apply, smul_eq_mul]
    exact (Measure.measurable_coe hs).const_mul c

/-- **Scaling of the Revuz measure**: the Revuz measure of the clock `c A` is `c` times that of `A`, when the
occupation kernel of `A` is measurable (supplied by `measurable_occupationMeasure_regularize`). -/
theorem revuz_const_mul {c : ℝ≥0} (hc : c ≠ 0) {W : ℂ → Measure (ContinuousPath ℂ)} (hW : Measurable W)
    {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hk : Measurable fun ω : ContinuousPath ℂ => occupationMeasure (fun t => regularize A t ω) ω) :
    revuz W (fun t ω => c * A t ω) = (c : ℝ≥0∞) • revuz W A := by
  have h0 : (c : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have hk' : ∀ ω, occupationMeasure (fun t => regularize (fun s ω' => c * A s ω') t ω) ω =
      (c : ℝ≥0∞) • occupationMeasure (fun t => regularize A t ω) ω := fun ω => by
    simp_rw [regularize_const_mul hc]
    exact occupationMeasure_const_mul hc _ ω
  have hkc : Measurable fun ω : ContinuousPath ℂ =>
      occupationMeasure (fun t => regularize (fun s ω' => c * A s ω') t ω) ω := by
    rw [show (fun ω : ContinuousPath ℂ => occupationMeasure (fun t => regularize (fun s ω' => c * A s ω') t ω) ω) =
      fun ω => (c : ℝ≥0∞) • occupationMeasure (fun t => regularize A t ω) ω from funext hk']
    exact (measurable_const_smul_measure _).comp hk
  ext S hS
  rw [revuz_apply hW hkc hS, Measure.smul_apply, revuz_apply hW hk hS, smul_eq_mul,
    ← lintegral_const_mul' _ _ h0]
  refine lintegral_congr fun z => ?_
  rw [← lintegral_const_mul' _ _ h0]
  refine lintegral_congr fun ω => ?_
  rw [hk' ω, Measure.smul_apply, smul_eq_mul]

/-- A constant multiple of a positive continuous additive functional is one. -/
theorem IsPCAF.const_mul {W : ℂ → Measure (ContinuousPath ℂ)} {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (h : IsPCAF W A) (c : ℝ≥0) : IsPCAF W (fun t ω => c * A t ω) where
  meas t := (h.meas t).const_mul c
  adapted z t := by
    obtain ⟨g, hg, hAg⟩ := h.adapted z t
    refine ⟨fun ω => c * g ω, hg.const_mul c, ?_⟩
    filter_upwards [hAg] with ω hω
    simp only [hω]
  path z := by
    filter_upwards [h.path z] with ω hω
    obtain ⟨h0, hcont, hm⟩ := hω
    exact ⟨by simp [h0], continuous_const.mul hcont, fun s t hst => mul_le_mul_of_nonneg_left (hm hst) (by positivity)⟩
  add z s t := by
    filter_upwards [h.add z s t] with ω hω
    simp only [hω, mul_add]

/-- A positive multiple of a good clock is a good clock. -/
theorem GoodClock.const_mul {W : ℂ → Measure (ContinuousPath ℂ)} {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (h : GoodClock W A) {c : ℝ≥0} (hc : c ≠ 0) : GoodClock W (fun t ω => c * A t ω) := fun z => by
  filter_upwards [h z] with ω hω
  obtain ⟨hs, ht⟩ := hω
  exact ⟨fun s t hst => mul_lt_mul_of_pos_left (hs hst) (pos_iff_ne_zero.2 hc),
    ht.const_mul_atTop' (pos_iff_ne_zero.2 hc)⟩

end MatedCRT
