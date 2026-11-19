import MatedCRT.FirstPass.Derived.RevuzShiftAdditivity
import MatedCRT.FirstPass.Derived.RevuzLintegral
import MatedCRT.FirstPass.Derived.RevuzLebesgueInvariance

/-!
# The Revuz measure as the rate of a clock on every unit time window

Let `A` be a positive continuous additive functional of planar Brownian motion. Along a path where `A` is
continuous and nondecreasing and additive at the time `t`, `A (t + s) = A t + B s` for all `s`, the Stieltjes
measure of `A` on `(t, t + 1]` is the translate by `t` of the Stieltjes measure of `B` on `(0, 1]`
(`stieltjesOfNNReal_measure_restrict_Ioc_shift`). With `B` the rational-time regularization of `A` along the
shifted path (`ae_add_regularize_pathShift`) and the invariance of `∫ P_z dz` under the time shift, this gives,
for every `t ≥ 0` and measurable `g ≥ 0`,

`∫ dz E_z ∫_{(t, t+1]} g(B_s) dA_s = ∫ g dμ_A`

(`lintegral_setLIntegral_Ioc_shift_eq_lintegral_revuz`; Revuz–Yor (1999), Chapter X, §2;
Fukushima–Oshima–Takeda (2011), (5.1.13) with `h ≡ 1`).
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess

/-- **Stieltjes function of a clock additive at a time `t`.** If `a (t + s) = a t + b s` for every `s`, for
continuous nondecreasing clocks `a, b`, then the Stieltjes function of `a` at `x ≥ t` is `a t` plus the Stieltjes
function of `b` at `x - t`. -/
theorem stieltjesOfNNReal_eq_add_of_shift {a b : ℝ≥0 → ℝ≥0} (ham : Monotone a) (hac : Continuous a)
    (hbm : Monotone b) (hbc : Continuous b) {t : ℝ≥0} (hshift : ∀ s, a (t + s) = a t + b s)
    {x : ℝ} (hx : (t : ℝ) ≤ x) :
    stieltjesOfNNReal a x = a t + stieltjesOfNNReal b (x - t) := by
  have hx0 : 0 ≤ x := t.coe_nonneg.trans hx
  have hsplit : x.toNNReal = t + (x - t).toNNReal := by
    apply NNReal.eq
    rw [NNReal.coe_add, Real.coe_toNNReal _ hx0, Real.coe_toNNReal _ (sub_nonneg.2 hx)]
    ring
  rw [stieltjesOfNNReal_apply_of_continuous ham hac, stieltjesOfNNReal_apply_of_continuous hbm hbc,
    hsplit, hshift, NNReal.coe_add]

/-- **The Stieltjes measure of an additive clock on a unit window.** If `a (t + s) = a t + b s` for every `s`, for
continuous nondecreasing clocks `a, b`, then the Stieltjes measure of `a` on `(t, t + 1]` is the image of the
Stieltjes measure of `b` on `(0, 1]` under the translation `s ↦ t + s`. -/
theorem stieltjesOfNNReal_measure_restrict_Ioc_shift {a b : ℝ≥0 → ℝ≥0} (ham : Monotone a)
    (hac : Continuous a) (hbm : Monotone b) (hbc : Continuous b) {t : ℝ≥0}
    (hshift : ∀ s, a (t + s) = a t + b s) :
    (stieltjesOfNNReal a).measure.restrict (Ioc (t : ℝ) (t + 1)) =
      ((stieltjesOfNNReal b).measure.restrict (Ioc 0 1)).map (fun s : ℝ => (t : ℝ) + s) := by
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
  have hIoc : ∀ u v : ℝ, (fa.measure.restrict (Ioc (t : ℝ) (t + 1))) (Ioc u v) =
      ((fb.measure.restrict (Ioc 0 1)).map fun s : ℝ => (t : ℝ) + s) (Ioc u v) := by
    intro u v
    rw [Measure.map_apply hmeas measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc, hpre,
      Measure.restrict_apply measurableSet_Ioc, Ioc_inter_Ioc, Ioc_inter_Ioc,
      StieltjesFunction.measure_Ioc, StieltjesFunction.measure_Ioc, hinc _ _ (le_max_right _ _)]
    have h1 : min v (t + 1) - t = min (v - t) 1 := by
      rw [← min_sub_sub_right, add_sub_cancel_left]
    have h2 : max u t - t = max (u - t) 0 := by
      rw [← max_sub_sub_right, sub_self]
    rw [h1, h2]
  have hfin : IsFiniteMeasure (fa.measure.restrict (Ioc (t : ℝ) (t + 1))) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have huniv : (fa.measure.restrict (Ioc (t : ℝ) (t + 1))) univ =
      ((fb.measure.restrict (Ioc 0 1)).map fun s : ℝ => (t : ℝ) + s) univ := by
    rw [Measure.map_apply hmeas MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ,
      Measure.restrict_apply_univ, StieltjesFunction.measure_Ioc, StieltjesFunction.measure_Ioc,
      hinc _ _ le_rfl, add_sub_cancel_left, sub_self]
  exact Measure.ext_of_Ioc_finite _ _ huniv fun u v _ => hIoc u v

/-- **Integral along a path over a unit window of an additive clock.** If `a (t + s) = a t + b s` for every `s`,
for continuous nondecreasing clocks `a, b`, then `∫_{(t, t+1]} g(ω_s) da_s = ∫_{(0,1]} g((θ_t ω)_s) db_s` for
measurable `g ≥ 0`. -/
theorem setLIntegral_Ioc_shift_eq {a b : ℝ≥0 → ℝ≥0} (ham : Monotone a) (hac : Continuous a)
    (hbm : Monotone b) (hbc : Continuous b) {t : ℝ≥0} (hshift : ∀ s, a (t + s) = a t + b s)
    (ω : ContinuousPath ℂ) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ s in Ioc (t : ℝ) (t + 1), g (ω s.toNNReal) ∂(stieltjesOfNNReal a).measure =
      ∫⁻ s in Ioc (0 : ℝ) 1, g (LatticeProb.pathShift ω t s.toNNReal) ∂(stieltjesOfNNReal b).measure := by
  rw [stieltjesOfNNReal_measure_restrict_Ioc_shift ham hac hbm hbc hshift,
    lintegral_map (show Measurable fun s : ℝ => g (ω s.toNNReal) from
      hg.comp (ω.continuous.comp continuous_real_toNNReal).measurable) (measurable_const_add _)]
  refine setLIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
  rw [LatticeProb.pathShift_apply, Real.toNNReal_add t.coe_nonneg hs.1.le, Real.toNNReal_coe]

/-- **The integral of a clock over a unit window is the occupation integral of the shifted path.** For a positive
continuous additive functional `A`, every starting point `z`, time `t` and measurable `g ≥ 0`, almost surely,
`∫_{(t, t+1]} g(ω_s) dA_s(ω)` is the integral of `g` against the occupation measure of the shifted path `θ_t ω`
for the regularized clock. -/
theorem ae_setLIntegral_Ioc_shift_eq_occupationMeasure {W : ℂ → Measure (ContinuousPath ℂ)}
    {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF W A) (z : ℂ) (t : ℝ≥0) {g : ℂ → ℝ≥0∞}
    (hg : Measurable g) :
    ∀ᵐ ω ∂W z, ∫⁻ s in Ioc (t : ℝ) (t + 1), g (ω s.toNNReal) ∂(stieltjesOfNNReal fun u => A u ω).measure =
      ∫⁻ x, g x ∂occupationMeasure (fun u => regularize A u (LatticeProb.pathShift ω t))
        (LatticeProb.pathShift ω t) := by
  filter_upwards [hA.path z, ae_add_regularize_pathShift hA z t] with ω hp hadd
  have hb : (fun s => regularize A s (LatticeProb.pathShift ω t)) = fun s => A (t + s) ω - A t ω := by
    funext s
    rw [hadd s, add_tsub_cancel_left]
  have hbc : Continuous fun s => regularize A s (LatticeProb.pathShift ω t) := by
    rw [hb]
    exact (hp.2.1.comp (continuous_const.add continuous_id)).sub continuous_const
  rw [lintegral_occupationMeasure _ _ hg]
  exact setLIntegral_Ioc_shift_eq hp.2.2 hp.2.1 (regularize_monotone A _) hbc hadd ω hg

/-- **The Revuz measure is the rate of the clock on every unit time window.** For a positive continuous additive
functional `A` of planar Brownian motion, every `t ≥ 0` and measurable `g ≥ 0`,
`∫ dz E_z ∫_{(t, t+1]} g(B_s) dA_s = ∫ g dμ_A`. -/
theorem lintegral_setLIntegral_Ioc_shift_eq_lintegral_revuz {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (t : ℝ≥0) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, ∫⁻ ω, ∫⁻ s in Ioc (t : ℝ) (t + 1), g (ω s.toNNReal)
        ∂(stieltjesOfNNReal fun u => A u ω).measure ∂planarLaw z =
      ∫⁻ x, g x ∂revuz planarLaw A := by
  have hF : Measurable fun ω' : ContinuousPath ℂ =>
      ∫⁻ x, g x ∂occupationMeasure (fun u => regularize A u ω') ω' :=
    (Measure.measurable_lintegral hg).comp (measurable_occupationMeasure_regularize hA.meas)
  rw [lintegral_revuz measurable_planarLaw hA.meas hg, ← lintegral_pathShift_planarLaw t hF]
  exact lintegral_congr fun z =>
    lintegral_congr_ae (ae_setLIntegral_Ioc_shift_eq_occupationMeasure hA z t hg)

end MatedCRT
