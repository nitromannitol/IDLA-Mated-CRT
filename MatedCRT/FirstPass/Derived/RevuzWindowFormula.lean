import MatedCRT.FirstPass.Derived.RevuzIntervalShift
import MatedCRT.FirstPass.Derived.RevuzKernel
import LatticeProb.Prob.StieltjesKernelInterval
import LatticeProb.Analysis.AdditiveENNRealHalfLine

/-!
# The Revuz measure is the rate of the clock on every time window

For a positive continuous additive functional `A` of planar Brownian motion with Revuz measure `μ_A` (with respect
to Lebesgue measure), every `t ≥ 0`, every window length `h ≥ 0` and every measurable `g ≥ 0`,
`∫ dz E_z ∫_{(t, t+h]} g(B_s) dA_s = h · ∫ g dμ_A`
(Revuz–Yor (1999), Chapter X, Proposition 2.4; Fukushima–Oshima–Takeda (2011), (5.1.13)).

The unit window `h = 1` is `lintegral_setLIntegral_Ioc_shift_eq_lintegral_revuz`. For general `h` the left side
does not depend on `t` (additivity of `A` at the fixed time `t` plus the invariance of the Lebesgue-started Brownian
motion under the shift `θ_t`), so it is an additive function of `h` on `[0, ∞)` with values in `[0, ∞]`, and
Cauchy's functional equation on the half-line gives `h` times its value at `h = 1`.

As in `RevuzIntervalShift`, the clock on the shifted path is the rational-time regularization `regularize A`,
which is measurable in the path; the raw clock appears only on the unshifted path.

## Main results

* `stieltjesOfNNReal_measure_restrict_Ioc_shift_window`, `setLIntegral_Ioc_shift_window_eq`: deterministic
  shift of a window `(t, t + h]` of an additive clock;
* `clockWindowIntegral A g h ω = ∫_{(0,h]} g(ω_s) dĀ_s(ω)` and its measurability;
* `ae_setLIntegral_Ioc_shift_window_eq`: almost surely `∫_{(t,t+h]} g(B_s) dA_s = ∫_{(0,h]} g((θ_t B)_s) dĀ_s(θ_t B)`;
* `lintegral_setLIntegral_Ioc_window_eq`: the Lebesgue-started window integral does not depend on `t`;
* `lintegral_clockWindowIntegral_add`: it is additive in the window length;
* `lintegral_setLIntegral_Ioc_eq_ofReal_mul_lintegral_revuz`: the window formula.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess

/-- **The Stieltjes measure of an additive clock on a window.** If `a (t + s) = a t + b s` for every `s`, for
continuous nondecreasing clocks `a, b`, then for every `h` the Stieltjes measure of `a` on `(t, t + h]` is the image
of the Stieltjes measure of `b` on `(0, h]` under the translation `s ↦ t + s`. -/
theorem stieltjesOfNNReal_measure_restrict_Ioc_shift_window {a b : ℝ≥0 → ℝ≥0} (ham : Monotone a)
    (hac : Continuous a) (hbm : Monotone b) (hbc : Continuous b) {t : ℝ≥0}
    (hshift : ∀ s, a (t + s) = a t + b s) (h : ℝ) :
    (stieltjesOfNNReal a).measure.restrict (Ioc (t : ℝ) (t + h)) =
      ((stieltjesOfNNReal b).measure.restrict (Ioc 0 h)).map (fun s : ℝ => (t : ℝ) + s) := by
  set fa := stieltjesOfNNReal a
  set fb := stieltjesOfNNReal b
  have key : ∀ x : ℝ, (t : ℝ) ≤ x → fa x = a t + fb (x - t) := fun x hx =>
    stieltjesOfNNReal_eq_add_of_shift ham hac hbm hbc hshift hx
  have hmeas : Measurable fun s : ℝ => (t : ℝ) + s := measurable_const_add _
  have hinc : ∀ x y : ℝ, (t : ℝ) ≤ x →
      ENNReal.ofReal (fa y - fa x) = ENNReal.ofReal (fb (y - t) - fb (x - t)) := by
    intro x y hx
    rcases le_or_gt x y with hxy | hxy
    · rw [key x hx, key y (hx.trans hxy), add_sub_add_left_eq_sub]
    · rw [ENNReal.ofReal_of_nonpos (sub_nonpos.2 (fa.mono hxy.le)),
        ENNReal.ofReal_of_nonpos (sub_nonpos.2 (fb.mono (by linarith)))]
  have hpre : ∀ u v : ℝ, (fun s : ℝ => (t : ℝ) + s) ⁻¹' Ioc u v = Ioc (u - t) (v - t) := by
    intro u v
    ext s
    simp only [mem_preimage, mem_Ioc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hIoc : ∀ u v : ℝ, (fa.measure.restrict (Ioc (t : ℝ) (t + h))) (Ioc u v) =
      ((fb.measure.restrict (Ioc 0 h)).map fun s : ℝ => (t : ℝ) + s) (Ioc u v) := by
    intro u v
    rw [Measure.map_apply hmeas measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc, hpre,
      Measure.restrict_apply measurableSet_Ioc, Ioc_inter_Ioc, Ioc_inter_Ioc,
      StieltjesFunction.measure_Ioc, StieltjesFunction.measure_Ioc, hinc _ _ (le_max_right _ _)]
    have h1 : min v (t + h) - t = min (v - t) h := by
      rw [← min_sub_sub_right, add_sub_cancel_left]
    have h2 : max u t - t = max (u - t) 0 := by
      rw [← max_sub_sub_right, sub_self]
    rw [h1, h2]
  have hfin : IsFiniteMeasure (fa.measure.restrict (Ioc (t : ℝ) (t + h))) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have huniv : (fa.measure.restrict (Ioc (t : ℝ) (t + h))) univ =
      ((fb.measure.restrict (Ioc 0 h)).map fun s : ℝ => (t : ℝ) + s) univ := by
    rw [Measure.map_apply hmeas MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ,
      Measure.restrict_apply_univ, StieltjesFunction.measure_Ioc, StieltjesFunction.measure_Ioc,
      hinc _ _ le_rfl, add_sub_cancel_left, sub_self]
  exact Measure.ext_of_Ioc_finite _ _ huniv fun u v _ => hIoc u v

/-- **Integral along a path over a window of an additive clock.** If `a (t + s) = a t + b s` for every `s`, for
continuous nondecreasing clocks `a, b`, then `∫_{(t, t+h]} g(ω_s) da_s = ∫_{(0,h]} g((θ_t ω)_s) db_s` for
measurable `g ≥ 0`. -/
theorem setLIntegral_Ioc_shift_window_eq {a b : ℝ≥0 → ℝ≥0} (ham : Monotone a) (hac : Continuous a)
    (hbm : Monotone b) (hbc : Continuous b) {t : ℝ≥0} (hshift : ∀ s, a (t + s) = a t + b s)
    (ω : ContinuousPath ℂ) {g : ℂ → ℝ≥0∞} (hg : Measurable g) (h : ℝ) :
    ∫⁻ s in Ioc (t : ℝ) (t + h), g (ω s.toNNReal) ∂(stieltjesOfNNReal a).measure =
      ∫⁻ s in Ioc (0 : ℝ) h, g (LatticeProb.pathShift ω t s.toNNReal) ∂(stieltjesOfNNReal b).measure := by
  rw [stieltjesOfNNReal_measure_restrict_Ioc_shift_window ham hac hbm hbc hshift h,
    lintegral_map (show Measurable fun s : ℝ => g (ω s.toNNReal) from
      hg.comp (ω.continuous.comp continuous_real_toNNReal).measurable) (measurable_const_add _)]
  refine setLIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
  rw [LatticeProb.pathShift_apply, Real.toNNReal_add t.coe_nonneg hs.1.le, Real.toNNReal_coe]

/-- The integral `∫_{(0,h]} g(ω_s) dĀ_s(ω)` of `g` along the path `ω` against the rational-time regularization
`Ā = regularize A` of the clock, over the window `(0, h]`. -/
noncomputable def clockWindowIntegral (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (g : ℂ → ℝ≥0∞) (h : ℝ)
    (ω : ContinuousPath ℂ) : ℝ≥0∞ :=
  ∫⁻ s in Ioc (0 : ℝ) h, g (ω s.toNNReal) ∂(stieltjesOfNNReal fun u => regularize A u ω).measure

/-- The regularized window integral is measurable in the path. -/
theorem measurable_clockWindowIntegral {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : ∀ t, Measurable (A t))
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) (h : ℝ) : Measurable (clockWindowIntegral A g h) :=
  LatticeProb.measurable_setLIntegral_stieltjes_Ioc_comp
    (fun ω : ContinuousPath ℂ => stieltjesOfNNReal (fun t => regularize A t ω))
    (measurable_stieltjesOfNNReal_regularize hA) (fun ω s => ω s.toNNReal)
    (fun ω => ω.continuous.comp continuous_real_toNNReal)
    (fun _ => ContinuousMap.measurable_eval _) 0 h hg

/-- **The clock integral over a window is the regularized window integral of the shifted path.** For a positive
continuous additive functional `A`, every starting point `z`, time `t`, window length `h` and measurable `g ≥ 0`,
almost surely `∫_{(t, t+h]} g(ω_s) dA_s(ω) = ∫_{(0,h]} g((θ_t ω)_s) dĀ_s(θ_t ω)`. -/
theorem ae_setLIntegral_Ioc_shift_window_eq {W : ℂ → Measure (ContinuousPath ℂ)}
    {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF W A) (z : ℂ) (t : ℝ≥0) {g : ℂ → ℝ≥0∞}
    (hg : Measurable g) (h : ℝ) :
    ∀ᵐ ω ∂W z, ∫⁻ s in Ioc (t : ℝ) (t + h), g (ω s.toNNReal) ∂(stieltjesOfNNReal fun u => A u ω).measure =
      clockWindowIntegral A g h (LatticeProb.pathShift ω t) := by
  filter_upwards [hA.path z, ae_add_regularize_pathShift hA z t] with ω hp hadd
  have hb : (fun s => regularize A s (LatticeProb.pathShift ω t)) = fun s => A (t + s) ω - A t ω := by
    funext s
    rw [hadd s, add_tsub_cancel_left]
  have hbc : Continuous fun s => regularize A s (LatticeProb.pathShift ω t) := by
    rw [hb]
    exact (hp.2.1.comp (continuous_const.add continuous_id)).sub continuous_const
  exact setLIntegral_Ioc_shift_window_eq hp.2.2 hp.2.1 (regularize_monotone A _) hbc hadd ω hg h

/-- The clock integral over a window is almost everywhere measurable in the path. -/
theorem aemeasurable_setLIntegral_Ioc_window {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (z : ℂ) (t : ℝ≥0) {g : ℂ → ℝ≥0∞} (hg : Measurable g) (h : ℝ) :
    AEMeasurable (fun ω : ContinuousPath ℂ => ∫⁻ s in Ioc (t : ℝ) (t + h), g (ω s.toNNReal)
      ∂(stieltjesOfNNReal fun u => A u ω).measure) (planarLaw z) :=
  ((measurable_clockWindowIntegral hA.meas hg h).comp (measurable_pathShift_const t)).aemeasurable.congr
    ((ae_setLIntegral_Ioc_shift_window_eq hA z t hg h).mono fun _ hω => hω.symm)

/-- The expected clock integral over a window is measurable in the starting point. -/
theorem measurable_lintegral_setLIntegral_Ioc_window {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (t : ℝ≥0) {g : ℂ → ℝ≥0∞} (hg : Measurable g) (h : ℝ) :
    Measurable fun z => ∫⁻ ω, ∫⁻ s in Ioc (t : ℝ) (t + h), g (ω s.toNNReal)
      ∂(stieltjesOfNNReal fun u => A u ω).measure ∂planarLaw z := by
  have heq : (fun z => ∫⁻ ω, ∫⁻ s in Ioc (t : ℝ) (t + h), g (ω s.toNNReal)
        ∂(stieltjesOfNNReal fun u => A u ω).measure ∂planarLaw z) =
      fun z => ∫⁻ ω, clockWindowIntegral A g h (LatticeProb.pathShift ω t) ∂planarLaw z :=
    funext fun z => lintegral_congr_ae (ae_setLIntegral_Ioc_shift_window_eq hA z t hg h)
  rw [heq]
  exact (Measure.measurable_lintegral ((measurable_clockWindowIntegral hA.meas hg h).comp
    (measurable_pathShift_const t))).comp measurable_planarLaw

/-- **The Lebesgue-started window integral does not depend on the start of the window.** For a positive continuous
additive functional `A` of planar Brownian motion, `∫ dz E_z ∫_{(t, t+h]} g(B_s) dA_s = ∫ dz E_z ∫_{(0,h]} g(B_s) dĀ_s`
for every `t ≥ 0` and `h`. -/
theorem lintegral_setLIntegral_Ioc_window_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (t : ℝ≥0) {g : ℂ → ℝ≥0∞} (hg : Measurable g) (h : ℝ) :
    ∫⁻ z, ∫⁻ ω, ∫⁻ s in Ioc (t : ℝ) (t + h), g (ω s.toNNReal)
        ∂(stieltjesOfNNReal fun u => A u ω).measure ∂planarLaw z =
      ∫⁻ z, ∫⁻ ω, clockWindowIntegral A g h ω ∂planarLaw z := by
  rw [← lintegral_pathShift_planarLaw t (measurable_clockWindowIntegral hA.meas hg h)]
  exact lintegral_congr fun z => lintegral_congr_ae (ae_setLIntegral_Ioc_shift_window_eq hA z t hg h)

/-- **Additivity in the window length.** `h ↦ ∫ dz E_z ∫_{(0,h]} g(B_s) dĀ_s` is additive on `[0, ∞)`. -/
theorem lintegral_clockWindowIntegral_add {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) {g : ℂ → ℝ≥0∞} (hg : Measurable g) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∫⁻ z, ∫⁻ ω, clockWindowIntegral A g (a + b) ω ∂planarLaw z =
      (∫⁻ z, ∫⁻ ω, clockWindowIntegral A g a ω ∂planarLaw z) +
        ∫⁻ z, ∫⁻ ω, clockWindowIntegral A g b ω ∂planarLaw z := by
  lift a to ℝ≥0 using ha
  rw [← lintegral_setLIntegral_Ioc_window_eq hA 0 hg ((a : ℝ) + b),
    ← lintegral_setLIntegral_Ioc_window_eq hA 0 hg (a : ℝ),
    ← lintegral_setLIntegral_Ioc_window_eq hA a hg b]
  have hz : ∀ z, ∫⁻ ω, ∫⁻ s in Ioc ((0 : ℝ≥0) : ℝ) ((0 : ℝ≥0) + ((a : ℝ) + b)), g (ω s.toNNReal)
        ∂(stieltjesOfNNReal fun u => A u ω).measure ∂planarLaw z =
      ∫⁻ ω, ∫⁻ s in Ioc ((0 : ℝ≥0) : ℝ) ((0 : ℝ≥0) + (a : ℝ)), g (ω s.toNNReal)
        ∂(stieltjesOfNNReal fun u => A u ω).measure ∂planarLaw z +
      ∫⁻ ω, ∫⁻ s in Ioc (a : ℝ) (a + b), g (ω s.toNNReal)
        ∂(stieltjesOfNNReal fun u => A u ω).measure ∂planarLaw z := by
    intro z
    rw [← lintegral_add_left' (aemeasurable_setLIntegral_Ioc_window hA z 0 hg (a : ℝ))]
    refine lintegral_congr fun ω => ?_
    rw [NNReal.coe_zero, zero_add, zero_add, ← lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl),
      Ioc_union_Ioc_eq_Ioc (NNReal.coe_nonneg a) (le_add_of_nonneg_right hb)]
  rw [lintegral_congr hz,
    lintegral_add_left (measurable_lintegral_setLIntegral_Ioc_window hA 0 hg (a : ℝ))]

/-- At window length `1` the Lebesgue-started regularized window integral is the integral against the Revuz
measure. -/
theorem lintegral_clockWindowIntegral_one {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, ∫⁻ ω, clockWindowIntegral A g 1 ω ∂planarLaw z = ∫⁻ y, g y ∂revuz planarLaw A := by
  rw [lintegral_revuz_of_isPCAF measurable_planarLaw hA hg,
    ← lintegral_setLIntegral_Ioc_window_eq hA 0 hg 1, NNReal.coe_zero, zero_add]

/-- **The window formula for the Revuz measure** (Revuz–Yor (1999), Chapter X, Proposition 2.4). For a positive
continuous additive functional `A` of planar Brownian motion, every `t ≥ 0`, `h ≥ 0` and measurable `g ≥ 0`,
`∫ dz E_z ∫_{(t, t+h]} g(B_s) dA_s = h · ∫ g dμ_A`. -/
theorem lintegral_setLIntegral_Ioc_eq_ofReal_mul_lintegral_revuz {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (t : ℝ≥0) {g : ℂ → ℝ≥0∞} (hg : Measurable g) {h : ℝ} (hh : 0 ≤ h) :
    ∫⁻ z, ∫⁻ ω, ∫⁻ s in Ioc (t : ℝ) (t + h), g (ω s.toNNReal)
        ∂(stieltjesOfNNReal fun u => A u ω).measure ∂planarLaw z =
      ENNReal.ofReal h * ∫⁻ y, g y ∂revuz planarLaw A := by
  rw [lintegral_setLIntegral_Ioc_window_eq hA t hg h, ← lintegral_clockWindowIntegral_one hA hg]
  rcases hh.lt_or_eq with hpos | rfl
  · exact LatticeProb.eq_ofReal_mul_of_add
      (m := fun h => ∫⁻ z, ∫⁻ ω, clockWindowIntegral A g h ω ∂planarLaw z)
      (fun a b ha hb => lintegral_clockWindowIntegral_add hA hg ha hb) hpos
  · simp [clockWindowIntegral]

end MatedCRT
