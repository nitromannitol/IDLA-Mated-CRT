import MatedCRT.FirstPass.S2y.LateralBilin250
import MatedCRT.FirstPass.S2y.CircleKernelSmooth250
import MatedCRT.FirstPass.S2y.LateralHc250

/-!
# The circle-smear identity of the whole-plane field

For a test function `φ` and a radius `ε > 0`, the smeared circle average `∫ φ(z) h_ε(z) dz` of a whole-plane GFF equals
the pairing `(h, K_ε φ)` with the circle kernel `K_ε φ = circleKernel φ ε`, almost surely (Duplantier-Sheffield 2011,
Section 3.1; Armitage-Gardiner, Fubini for the adjoint of the circle average).

The proof is an L² argument: `J := ∫ φ h_ε` is square integrable, and `E[(J - (h, K_ε φ))²] = 0`
by Fubini on the second moments `wholePlaneGFFCov`.

This file contains the covariance identities of circle averages (`integral_mul_circle_circle`,
`integral_mul_circle_pairing`), reduced to `IsWholePlaneGFF.covariance_eq` as in `LateralBilin250.integral_mul_pairing`.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology Real Metric HarmonicBalls
open scoped ENNReal

namespace MatedCRT.LQGMeasure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The a.s. circle-smear identity for the whole-plane field: the smeared circle average
`∫ φ(z) h_ε(z) dz` is the pairing `(h, K_ε φ)` of the circle kernel `K_ε φ = circleKernel φ ε`. -/
def CircleSmearIdentity (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (φ : ℂ → ℝ) (ε : ℝ) :
    Prop :=
  ∀ᵐ ω ∂P, ∫ z, φ z * hcirc ω ε z = hC ω (circleKernel φ ε)

/-- The second moment of two circle averages of positive radius is the double circle average of `wholePlaneCov`
(the covariance of `IsWholePlaneGFF`, both observables centred). -/
lemma integral_mul_circle_circle [IsProbabilityMeasure P] (h : IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε)
    (z w : ℂ) :
    ∫ ω, hcirc ω ε z * hcirc ω ε w ∂P =
      Real.circleAverage (fun x => Real.circleAverage (fun y => wholePlaneCov x y) w ε) z ε := by
  have hc : cov[fun ω => hcirc ω ε z, fun ω => hcirc ω ε w; P] =
      Real.circleAverage (fun x => Real.circleAverage (fun y => wholePlaneCov x y) w ε) z ε :=
    h.covariance_eq (.circle ε z) (.circle ε w) hε hε
  have h0z : ∫ ω, hcirc ω ε z ∂P = 0 := h.integral_eq_zero (.circle ε z) hε
  have h0w : ∫ ω, hcirc ω ε w ∂P = 0 := h.integral_eq_zero (.circle ε w) hε
  rw [← hc]
  simp only [covariance, h0z, h0w, sub_zero]

/-- The second moment of a circle average of positive radius and a pairing with a test function is the circle average
of the potential `x ↦ ∫ ψ(y) wholePlaneCov x y dy`. -/
lemma integral_mul_circle_pairing [IsProbabilityMeasure P] (h : IsWholePlaneGFF P hC hcirc) {ψ : ℂ → ℝ}
    (hψ : IsTestFunction univ ψ) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    ∫ ω, hcirc ω ε z * hC ω ψ ∂P =
      Real.circleAverage (fun x => ∫ y, ψ y * wholePlaneCov x y) z ε := by
  have hc : cov[fun ω => hcirc ω ε z, fun ω => hC ω ψ; P] =
      Real.circleAverage (fun x => ∫ y, ψ y * wholePlaneCov x y) z ε :=
    h.covariance_eq (.circle ε z) (.pairing ψ) hε hψ
  have h0z : ∫ ω, hcirc ω ε z ∂P = 0 := h.integral_eq_zero (.circle ε z) hε
  have h0ψ : ∫ ω, hC ω ψ ∂P = 0 := h.integral_eq_zero (.pairing ψ) hψ
  rw [← hc]
  simp only [covariance, h0z, h0ψ, sub_zero]

/-- Pointwise bound (equality off the diagonal): `wholePlaneCov x y ≤ log max(|x|,1) + log max(|y|,1) - log|x - y|`. -/
lemma wholePlaneCov_le_log (x y : ℂ) :
    wholePlaneCov x y ≤ Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1) - Real.log ‖x - y‖ := by
  unfold wholePlaneCov
  by_cases hxy : x = y
  · subst hxy
    simp only [sub_self, norm_zero, Real.log_zero, div_zero]
    have h1 : 0 ≤ Real.log (max ‖x‖ 1) := Real.log_nonneg (le_max_right _ _)
    linarith
  · have hc : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
    have hA : max ‖x‖ 1 ≠ 0 := (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
    have hB : max ‖y‖ 1 ≠ 0 := (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
    have h1 := Real.log_div (mul_ne_zero hA hB) hc
    have h2 := Real.log_mul hA hB
    linarith

/-- Mean value property of `log‖· - x‖` at a point `x` of the circle `∂B_ε(z)`: the circle average is `log ε`. -/
lemma circleAverage_log_norm_sub_of_mem_sphere {z x : ℂ} {ε : ℝ} (hε : 0 < ε) (hx : ‖z - x‖ = ε) :
    Real.circleAverage (fun y => Real.log ‖y - x‖) z ε = Real.log ε := by
  rw [MatedCRT.Field.circleAverage_log_norm_eq z x hε, hx, inv_mul_cancel₀ hε.ne']
  simp [Real.posLog]

/-- **Circle average of the covariance at a point of the circle.** For `x` on `∂B_ε(z)`, the average over `y ∈ ∂B_ε(z)`
of `wholePlaneCov x y` is `log max(|x|,1) + avg log max(|y|,1) - log ε` (the mean value property of `log|·-x|`,
Duplantier-Sheffield 2011, Section 3.1). The diagonal `y = x` is a single point, hence codiscrete on the circle. -/
lemma circleAverage_wholePlaneCov_of_mem_sphere {z x : ℂ} {ε : ℝ} (hε : 0 < ε) (hx : ‖z - x‖ = ε) :
    Real.circleAverage (fun y => wholePlaneCov x y) z ε =
      Real.log (max ‖x‖ 1) + Real.circleAverage (fun y => Real.log (max ‖y‖ 1)) z ε - Real.log ε := by
  have hcongr : (fun y => wholePlaneCov x y) =ᶠ[codiscreteWithin (sphere z |ε|)]
      (fun y => (Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1)) - Real.log ‖y - x‖) := by
    refine MatedCRT.CirclePairing.eventuallyEq_codiscreteWithin_of_ne _ x fun y hy => ?_
    unfold wholePlaneCov
    have hc : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy.symm)
    have hA : max ‖x‖ 1 ≠ 0 := (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
    have hB : max ‖y‖ 1 ≠ 0 := (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
    rw [Real.log_div (mul_ne_zero hA hB) hc, Real.log_mul hA hB, norm_sub_rev y x]
  have hlogB : Continuous fun y : ℂ => Real.log (max ‖y‖ 1) :=
    Continuous.log (by fun_prop) fun y => (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  have hI1 : CircleIntegrable (fun y : ℂ => Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1)) z ε :=
    ((continuous_const.add hlogB).continuousOn).circleIntegrable hε.le
  have hI2 : CircleIntegrable (fun y : ℂ => Real.log ‖y - x‖) z ε :=
    circleIntegrable_log_norm_sub_const (a := x) (c := z) ε
  rw [Real.circleAverage_congr_codiscreteWithin hcongr hε.ne']
  have hs : Real.circleAverage (fun y => (Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1)) - Real.log ‖y - x‖) z ε =
      Real.circleAverage (fun y => Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1)) z ε -
        Real.circleAverage (fun y => Real.log ‖y - x‖) z ε :=
    Real.circleAverage_sub hI1 hI2
  have hadd : Real.circleAverage (fun y => Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1)) z ε =
      Real.log (max ‖x‖ 1) + Real.circleAverage (fun y => Real.log (max ‖y‖ 1)) z ε := by
    have := Real.circleAverage_add (circleIntegrable_const (Real.log (max ‖x‖ 1)) z ε)
      (hlogB.continuousOn.circleIntegrable hε.le)
    rw [Real.circleAverage_const] at this
    exact this
  rw [hs, hadd, circleAverage_log_norm_sub_of_mem_sphere hε hx]

/-- **Sup bound for the circle averages**: for `‖z‖ ≤ R`, the second moment of the circle average
of radius `ε` is bounded uniformly, `E[h_ε(z)²] ≤ 2 log max(R + ε, 1) - log ε`. -/
lemma integral_sq_circle_le [IsProbabilityMeasure P] (h : IsWholePlaneGFF P hC hcirc) {R ε : ℝ} (hε : 0 < ε)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ∫ ω, hcirc ω ε z ^ 2 ∂P ≤ 2 * Real.log (max (R + ε) 1) - Real.log ε := by
  have hsq : (fun ω => hcirc ω ε z ^ 2) = fun ω => hcirc ω ε z * hcirc ω ε z := funext fun ω => sq _
  rw [hsq, integral_mul_circle_circle h hε z z]
  have habs : |ε| = ε := abs_of_pos hε
  have hlogB : Continuous fun y : ℂ => Real.log (max ‖y‖ 1) :=
    Continuous.log (by fun_prop) fun y => (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  -- on the circle `∂B_ε(z)`, `|y| ≤ R + ε`, so `log max(|y|,1) ≤ log max(R+ε,1)`
  have hLpt : ∀ y : ℂ, ‖y - z‖ ≤ ε → Real.log (max ‖y‖ 1) ≤ Real.log (max (R + ε) 1) := by
    intro y hy
    apply Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right _ _))
    apply max_le_max _ le_rfl
    have hsplit : z + (y - z) = y := by ring
    calc ‖y‖ = ‖z + (y - z)‖ := by rw [hsplit]
      _ ≤ ‖z‖ + ‖y - z‖ := norm_add_le _ _
      _ ≤ R + ε := by linarith
  have hsph : ∀ x ∈ Metric.sphere z |ε|, ‖z - x‖ = ε := fun x hx => by
    rw [mem_sphere_iff_norm] at hx
    rw [norm_sub_rev, hx, habs]
  have hEq : Set.EqOn (fun x => Real.circleAverage (fun y => wholePlaneCov x y) z ε)
      (fun x => Real.log (max ‖x‖ 1) + Real.circleAverage (fun y => Real.log (max ‖y‖ 1)) z ε - Real.log ε)
      (Metric.sphere z |ε|) := fun x hx => circleAverage_wholePlaneCov_of_mem_sphere hε (hsph x hx)
  rw [Real.circleAverage_congr_sphere hEq]
  have hB : Real.circleAverage (fun y => Real.log (max ‖y‖ 1)) z ε ≤ Real.log (max (R + ε) 1) :=
    Real.circleAverage_mono_on_of_le_circle (hlogB.continuousOn.circleIntegrable hε.le) fun y hy => by
      rw [mem_sphere_iff_norm, habs] at hy
      exact hLpt y hy.le
  have hFint : CircleIntegrable (fun x : ℂ => Real.log (max ‖x‖ 1) +
      Real.circleAverage (fun y => Real.log (max ‖y‖ 1)) z ε - Real.log ε) z ε :=
    ((hlogB.add continuous_const).sub continuous_const).continuousOn.circleIntegrable hε.le
  refine Real.circleAverage_mono_on_of_le_circle hFint fun x hx => ?_
  have hxz : ‖x - z‖ ≤ ε := by
    rw [mem_sphere_iff_norm, habs] at hx
    exact hx.le
  linarith [hLpt x hxz, hB]

/-- **Joint measurability of the circle averages**. For `ε > 0` there is a jointly measurable
version `g` of `(ω, z) ↦ hcirc ω ε z`, continuous in `z` for every `ω`, equal to it almost surely: the event of continuity
of the circle average process (`IsWholePlaneGFF.ae_continuousOn_circle`) is enlarged to a measurable null set `S`, and
`g = 0` off the complement of `S`. -/
lemma exists_measurable_circle [IsProbabilityMeasure P] (h : IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Ω → ℂ → ℝ, Measurable (fun p : Ω × ℂ => g p.1 p.2) ∧ (∀ ω, Continuous fun z => g ω z) ∧
      ∀ᵐ ω ∂P, ∀ z, g ω z = hcirc ω ε z := by
  obtain ⟨S, hsub, hSm, hS0⟩ := exists_measurable_superset_of_null (ae_iff.1 h.ae_continuousOn_circle)
  have hcont_all : ∀ ω, Continuous fun z => Sᶜ.indicator (fun ω' => hcirc ω' ε z) ω := by
    intro ω
    by_cases hω : ω ∈ Sᶜ
    · simp only [Set.indicator_of_mem hω]
      have hc : ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) := by
        by_contra hn
        exact hω (hsub hn)
      exact hc.comp_continuous (f := fun z : ℂ => ((ε, z) : ℝ × ℂ))
        (continuous_const.prodMk continuous_id) (fun z => ⟨hε, mem_univ _⟩)
    · simp only [Set.indicator_of_notMem hω]
      exact continuous_const
  refine ⟨fun ω z => Sᶜ.indicator (fun ω' => hcirc ω' ε z) ω, ?_, hcont_all, ?_⟩
  · have hm : Measurable (Function.uncurry fun (z : ℂ) (ω : Ω) => Sᶜ.indicator (fun ω' => hcirc ω' ε z) ω) :=
      measurable_uncurry_of_continuous_of_measurable (fun ω => hcont_all ω)
        (fun z => (h.measurable_circle ε z hε).indicator hSm.compl)
    exact hm.comp measurable_swap
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hS0] with ω hω
    intro z
    show Sᶜ.indicator (fun ω' => hcirc ω' ε z) ω = hcirc ω ε z
    rw [Set.indicator_of_mem (show ω ∈ Sᶜ from hω)]


/-! ### Deterministic part: the covariance kernel integrated against circle averages -/

/-- `y ↦ wholePlaneCov x y` is measurable. -/
lemma measurable_wholePlaneCov_right (x : ℂ) : Measurable fun y => wholePlaneCov x y := by
  unfold wholePlaneCov
  fun_prop

/-- `y ↦ wholePlaneCov x y` is locally integrable (its logarithmic singularity at `x` is integrable). -/
lemma locallyIntegrable_wholePlaneCov_right (x : ℂ) :
    LocallyIntegrable (fun y => wholePlaneCov x y) volume := by
  refine locallyIntegrable_iff.2 fun k hk => ?_
  obtain ⟨R, hR⟩ := hk.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨χ, hχ, hχ1⟩ := exists_test_one_on_ball R
  have hlog : IntegrableOn (fun y => Real.log ‖y - x‖) k := by
    refine ((HarmonicBalls.S11c.integrable_mul_logNorm_sub hχ x).integrableOn).congr_fun (fun y hy => ?_) hk.measurableSet
    simp only [hχ1 y (hR hy), one_mul]
  have hlogB : Continuous fun y : ℂ => Real.log (max ‖y‖ 1) :=
    Continuous.log (by fun_prop) fun y => (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  have hrhs : IntegrableOn (fun y => (Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1)) - Real.log ‖y - x‖) k :=
    ((continuous_const.add hlogB).continuousOn.integrableOn_compact hk).sub hlog
  have hae : ∀ᵐ y ∂(volume : Measure ℂ), y ≠ x := by
    rw [ae_iff]
    simp
  refine hrhs.congr_fun_ae ?_
  refine ae_restrict_of_ae ?_
  filter_upwards [hae] with y hy
  have hc : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy.symm)
  have hA : max ‖x‖ 1 ≠ 0 := (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  have hB : max ‖y‖ 1 ≠ 0 := (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  unfold wholePlaneCov
  rw [Real.log_div (mul_ne_zero hA hB) hc, Real.log_mul hA hB, norm_sub_rev y x]

/-- **Mean value of the covariance kernel over a circle** (general centre, Duplantier-Sheffield 2011, Section 3.1):
for every `x` and centre `w`, the average over `∂B_ε(w)` of `wholePlaneCov x` is
`log max(|x|,1) + avg_{∂B_ε(w)} log max(|·|,1) - (log ε + posLog(ε⁻¹ |w - x|))`. The diagonal `y = x` is codiscrete. -/
lemma circleAverage_wholePlaneCov_eq {ε : ℝ} (hε : 0 < ε) (x w : ℂ) :
    Real.circleAverage (fun y => wholePlaneCov x y) w ε =
      Real.log (max ‖x‖ 1) + Real.circleAverage (fun y => Real.log (max ‖y‖ 1)) w ε
        - (Real.log ε + Real.posLog (ε⁻¹ * ‖w - x‖)) := by
  have hlogB : Continuous fun y : ℂ => Real.log (max ‖y‖ 1) :=
    Continuous.log (by fun_prop) fun y => (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  have hcongr : (fun y => wholePlaneCov x y) =ᶠ[codiscreteWithin (sphere w |ε|)]
      (fun y => (Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1)) - Real.log ‖y - x‖) := by
    refine MatedCRT.CirclePairing.eventuallyEq_codiscreteWithin_of_ne _ x fun y hy => ?_
    unfold wholePlaneCov
    have hc : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy.symm)
    have hA : max ‖x‖ 1 ≠ 0 := (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
    have hB : max ‖y‖ 1 ≠ 0 := (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
    rw [Real.log_div (mul_ne_zero hA hB) hc, Real.log_mul hA hB, norm_sub_rev y x]
  rw [Real.circleAverage_congr_codiscreteWithin hcongr hε.ne']
  have hI1 : CircleIntegrable (fun y : ℂ => Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1)) w ε :=
    ((continuous_const.add hlogB).continuousOn).circleIntegrable hε.le
  have hI2 : CircleIntegrable (fun y : ℂ => Real.log ‖y - x‖) w ε :=
    circleIntegrable_log_norm_sub_const (a := x) (c := w) ε
  have hs : Real.circleAverage (fun y => (Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1)) - Real.log ‖y - x‖) w ε =
      Real.circleAverage (fun y => Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1)) w ε -
        Real.circleAverage (fun y => Real.log ‖y - x‖) w ε :=
    Real.circleAverage_sub hI1 hI2
  have hadd : Real.circleAverage (fun y => Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1)) w ε =
      Real.log (max ‖x‖ 1) + Real.circleAverage (fun y => Real.log (max ‖y‖ 1)) w ε := by
    have := Real.circleAverage_add (circleIntegrable_const (Real.log (max ‖x‖ 1)) w ε)
      (hlogB.continuousOn.circleIntegrable hε.le)
    rw [Real.circleAverage_const] at this
    exact this
  rw [hs, hadd, MatedCRT.Field.circleAverage_log_norm_eq w x hε]

/-- The covariance circle average `(x, w) ↦ ⨍_{∂B_ε(w)} wholePlaneCov x ·` is jointly continuous. -/
lemma continuous_circleAverage_wholePlaneCov {ε : ℝ} (hε : 0 < ε) :
    Continuous fun p : ℂ × ℂ => Real.circleAverage (fun y => wholePlaneCov p.1 y) p.2 ε := by
  have hlogB : Continuous fun y : ℂ => Real.log (max ‖y‖ 1) :=
    Continuous.log (by fun_prop) fun y => (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  have hc : Continuous fun w : ℂ => Real.circleAverage (fun y => Real.log (max ‖y‖ 1)) w ε :=
    continuous_circleAverage_center hlogB ε
  have hA : Continuous fun p : ℂ × ℂ => Real.log (max ‖p.1‖ 1) :=
    Continuous.log (by fun_prop) fun p => (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  have hP : Continuous fun p : ℂ × ℂ => Real.posLog (ε⁻¹ * ‖p.2 - p.1‖) :=
    Real.continuous_posLog.comp (continuous_const.mul (by fun_prop))
  have heq : (fun p : ℂ × ℂ => Real.circleAverage (fun y => wholePlaneCov p.1 y) p.2 ε) =
      fun p => Real.log (max ‖p.1‖ 1) + Real.circleAverage (fun y => Real.log (max ‖y‖ 1)) p.2 ε
        - (Real.log ε + Real.posLog (ε⁻¹ * ‖p.2 - p.1‖)) :=
    funext fun p => circleAverage_wholePlaneCov_eq hε p.1 p.2
  rw [heq]
  exact (hA.add (hc.comp continuous_snd)).sub (continuous_const.add hP)

/-- **Adjoint on the covariance kernel** (the one-variable adjoint of the circle average, `ConeApproxIdentity`):
for a test function `φ` and `0 < ε ≤ 1`, `∫ φ(w) ⨍_{∂B_ε(w)} wholePlaneCov x · dw = ∫ K_ε φ(y) wholePlaneCov x y dy`. -/
lemma adjoint_wholePlaneCov {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (x : ℂ) :
    ∫ w, φ w * Real.circleAverage (fun y => wholePlaneCov x y) w ε =
      ∫ y, circleKernel φ ε y * wholePlaneCov x y := by
  rw [integral_mul_circleAverage_eq (measurable_wholePlaneCov_right x) (locallyIntegrable_wholePlaneCov_right x)
    hφ.1.continuous hφ.2.1 hε hε1]
  congr 1
  funext y
  ring

/-- Measurability of the potential `x ↦ ∫ ψ(y) wholePlaneCov x y dy` of a test function `ψ`. -/
lemma measurable_potential {ψ : ℂ → ℝ} (hψ : IsTestFunction univ ψ) :
    Measurable fun x => ∫ y, ψ y * wholePlaneCov x y := by
  have hm : Measurable fun p : ℂ × ℂ => ψ p.2 * wholePlaneCov p.1 p.2 := by
    have h1 : Measurable fun p : ℂ × ℂ => ψ p.2 := hψ.1.continuous.measurable.comp measurable_snd
    have h2 : Measurable fun p : ℂ × ℂ => wholePlaneCov p.1 p.2 := by
      unfold wholePlaneCov
      fun_prop
    exact h1.mul h2
  exact (hm.stronglyMeasurable.integral_prod_right (ν := volume)).measurable

/-- Local integrability of the potential of a test function (Fubini on `integrable_prod_wholePlaneCov`). -/
lemma locallyIntegrable_potential {ψ : ℂ → ℝ} (hψ : IsTestFunction univ ψ) :
    LocallyIntegrable (fun x => ∫ y, ψ y * wholePlaneCov x y) volume := by
  refine locallyIntegrable_iff.2 fun k hk => ?_
  obtain ⟨R, hR⟩ := hk.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨χ, hχ, hχ1⟩ := exists_test_one_on_ball R
  have hJ : Integrable (fun x => ∫ y, χ x * ψ y * wholePlaneCov x y) :=
    (integrable_prod_wholePlaneCov hχ hψ).integral_prod_left
  refine (hJ.integrableOn).congr_fun (fun x hx => ?_) hk.measurableSet
  simp only [hχ1 x (hR hx), one_mul]

/-- **Fubini on the circle** (Armitage-Gardiner, Fubini for the circle average): for a jointly continuous `F`, the test
integral of a circle average in the first variable is the circle average of the test integrals. The cutoff `χ`
(a bump equal to `1` on `(0, 2π]`) makes the θ-integrand compactly supported. -/
lemma integral_mul_circleAverage_comm {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) (z : ℂ) (ε : ℝ)
    {F : ℂ → ℂ → ℝ} (hF : Continuous fun p : ℂ × ℂ => F p.1 p.2) :
    ∫ w, φ w * Real.circleAverage (fun x => F x w) z ε =
      Real.circleAverage (fun x => ∫ w, φ w * F x w) z ε := by
  set χ : ContDiffBump (π : ℝ) :=
    { rIn := π, rOut := 2 * π, rIn_pos := Real.pi_pos, rIn_lt_rOut := by linarith [Real.pi_pos] } with hχdef
  have hχ1 : ∀ θ ∈ Ioc (0 : ℝ) (2 * π), χ θ = 1 := by
    intro θ hθ
    refine χ.one_of_mem_closedBall ?_
    show θ ∈ Metric.closedBall (π : ℝ) π
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    constructor <;> linarith [hθ.1, hθ.2]
  have hcm : Continuous fun θ : ℝ => circleMap z ε θ := by fun_prop
  have hφc : Continuous φ := hφ.1.continuous
  have hcont : Continuous fun p : ℝ × ℂ => χ p.1 * (φ p.2 * F (circleMap z ε p.1) p.2) :=
    (χ.continuous.comp continuous_fst).mul
      ((hφc.comp continuous_snd).mul (hF.comp ((hcm.comp continuous_fst).prodMk continuous_snd)))
  have hsupp : HasCompactSupport
      (Function.uncurry fun (θ : ℝ) (w : ℂ) => χ θ * (φ w * F (circleMap z ε θ) w)) := by
    refine HasCompactSupport.intro (χ.hasCompactSupport.isCompact.prod hφ.2.1.isCompact) ?_
    intro p hp
    rw [Set.mem_prod, not_and_or] at hp
    show χ p.1 * (φ p.2 * F (circleMap z ε p.1) p.2) = 0
    rcases hp with h | h
    · simp [image_eq_zero_of_notMem_tsupport h]
    · simp [image_eq_zero_of_notMem_tsupport h]
  have hswap := integral_integral_swap_of_hasCompactSupport (μ := volume.restrict (Ioc (0 : ℝ) (2 * π)))
    (ν := (volume : Measure ℂ)) (f := fun (θ : ℝ) (w : ℂ) => χ θ * (φ w * F (circleMap z ε θ) w))
    hcont hsupp
  have key : ∀ w, φ w * Real.circleAverage (fun x => F x w) z ε
      = (2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), χ θ * (φ w * F (circleMap z ε θ) w) := by
    intro w
    have h1 : ∫ θ in Ioc 0 (2 * π), χ θ * (φ w * F (circleMap z ε θ) w)
        = ∫ θ in Ioc 0 (2 * π), φ w * F (circleMap z ε θ) w :=
      setIntegral_congr_fun measurableSet_Ioc fun θ hθ => by rw [hχ1 θ hθ, one_mul]
    rw [h1, integral_const_mul]
    unfold Real.circleAverage
    simp only [smul_eq_mul]
    rw [intervalIntegral.integral_of_le (by positivity)]
    ring
  calc ∫ w, φ w * Real.circleAverage (fun x => F x w) z ε
      = ∫ w, (2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), χ θ * (φ w * F (circleMap z ε θ) w) :=
        integral_congr_ae (Eventually.of_forall key)
    _ = (2 * π)⁻¹ * ∫ w, ∫ θ in Ioc 0 (2 * π), χ θ * (φ w * F (circleMap z ε θ) w) :=
        integral_const_mul _ _
    _ = (2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), ∫ w, χ θ * (φ w * F (circleMap z ε θ) w) :=
        congrArg (fun t => (2 * π)⁻¹ * t) hswap.symm
    _ = (2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), ∫ w, φ w * F (circleMap z ε θ) w := by
        congr 1
        refine setIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
        simp only [hχ1 θ hθ, one_mul]
    _ = Real.circleAverage (fun x => ∫ w, φ w * F x w) z ε := by
        unfold Real.circleAverage
        simp only [smul_eq_mul]
        rw [intervalIntegral.integral_of_le (by positivity)]

/-- **Two-step adjoint on the covariance kernel**: for a test function `φ`, `0 < ε ≤ 1` and any `z`,
`∫ φ(w) C_ε(z,w) dw = ⨍_{∂B_ε(z)} G_{K_ε φ}`, where `C_ε(z,w) = ⨍_{x∈∂B_ε(z)} ⨍_{y∈∂B_ε(w)} wholePlaneCov x y`
(the covariance of two circle averages, `integral_mul_circle_circle`). -/
lemma integral_mul_circleAverage_circleAverage_eq {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (z : ℂ) :
    ∫ w, φ w * Real.circleAverage (fun x => Real.circleAverage (fun y => wholePlaneCov x y) w ε) z ε =
      Real.circleAverage (fun x => ∫ y, circleKernel φ ε y * wholePlaneCov x y) z ε := by
  refine (integral_mul_circleAverage_comm hφ z ε
    (F := fun x w => Real.circleAverage (fun y => wholePlaneCov x y) w ε)
    (continuous_circleAverage_wholePlaneCov hε)).trans ?_
  congr 1
  funext x
  exact adjoint_wholePlaneCov hφ hε hε1 x

/-- **Adjoint for the potential** (the kernel `ψ = K_ε φ`): `∫ φ(z) ⨍_{∂B_ε(z)} G_ψ = ∫ ψ(x) G_ψ(x) dx`,
`G_ψ(x) = ∫ ψ(y) wholePlaneCov x y dy`. -/
lemma adjoint_potential {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hψ : IsTestFunction univ (circleKernel φ ε)) :
    ∫ z, φ z * Real.circleAverage (fun x => ∫ y, circleKernel φ ε y * wholePlaneCov x y) z ε =
      ∫ x, circleKernel φ ε x * ∫ y, circleKernel φ ε y * wholePlaneCov x y := by
  rw [integral_mul_circleAverage_eq (measurable_potential hψ) (locallyIntegrable_potential hψ)
    hφ.1.continuous hφ.2.1 hε hε1]
  congr 1
  funext x
  ring

/-! ### Random part: the `L²` argument for the smeared circle average `J := ∫ φ h_ε` -/

/-- Discriminant form of Cauchy-Schwarz: if `2ct ≤ t²a + b` for all `t > 0` with `a, b, c ≥ 0`, then `c² ≤ ab`. -/
lemma sq_le_mul_of_forall_two_mul_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : ∀ t : ℝ, 0 < t → 2 * c * t ≤ t ^ 2 * a + b) : c ^ 2 ≤ a * b := by
  rcases hc.eq_or_lt with hc0 | hc0
  · rw [← hc0]
    simpa using mul_nonneg ha hb
  have hc' : c ≠ 0 := hc0.ne'
  rcases ha.eq_or_lt with ha0 | ha0
  · exfalso
    have ht : 0 < (b + 1) / (2 * c) := div_pos (by linarith) (by linarith)
    have h1 := h _ ht
    have e : 2 * c * ((b + 1) / (2 * c)) = b + 1 := by field_simp
    rw [e, ← ha0, mul_zero, zero_add] at h1
    linarith
  · have ha' : a ≠ 0 := ha0.ne'
    have ht : 0 < c / a := div_pos hc0 ha0
    have h1 := h _ ht
    have e1 : 2 * c * (c / a) = 2 * (c ^ 2 / a) := by ring
    have e2 : (c / a) ^ 2 * a = c ^ 2 / a := by field_simp
    rw [e1, e2] at h1
    have h3 : c ^ 2 / a ≤ b := by linarith
    rw [div_le_iff₀ ha0] at h3
    linarith [mul_comm a b]

/-- Each circle average of positive radius, at any centre, is square integrable (the field is Gaussian). -/
lemma memLp_circle_any (h : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    MemLp (fun ω => hcirc ω r z) 2 P :=
  (MatedCRT.Field.wpSpace_gaussian h).memLp (Submodule.subset_span ⟨⟨GFFObservable.circle r z, hr⟩, rfl⟩)

/-- The measurable version `g` of the circle averages is square integrable at each point. -/
lemma memLp_of_ae_circle (h : IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε) {g : Ω → ℂ → ℝ}
    (hg : ∀ᵐ ω ∂P, ∀ z, g ω z = hcirc ω ε z) (z : ℂ) : MemLp (fun ω => g ω z) 2 P :=
  (memLp_circle_any h hε z).ae_eq (hg.mono fun _ hω => (hω z).symm)

/-- **Fubini for the smeared circle average** against a square integrable variable `X`:
`E[X · ∫ φ(z) g(z) dz] = ∫ φ(z) E[X g(z)] dz` (`integral_mul_integral_swap`, `X ∈ L²`). -/
lemma integral_mul_smear_swap [IsProbabilityMeasure P] (h : IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε)
    {g : Ω → ℂ → ℝ} (hgm : Measurable fun p : Ω × ℂ => g p.1 p.2)
    (hg : ∀ᵐ ω ∂P, ∀ z, g ω z = hcirc ω ε z) {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ)
    {X : Ω → ℝ} (hX : MemLp X 2 P) :
    ∫ ω, X ω * (∫ z, φ z * g ω z) ∂P = ∫ z, φ z * ∫ ω, X ω * g ω z ∂P := by
  obtain ⟨R, hR⟩ := hφ.2.1.isCompact.isBounded.subset_closedBall (0 : ℂ)
  have hgR : ∀ z, φ z ≠ 0 → ‖z‖ ≤ R := fun z hz =>
    mem_closedBall_zero_iff.1 (hR (subset_tsupport φ (Function.mem_support.2 hz)))
  have hAL2 : ∀ᵐ y ∂(volume.restrict (closedBall (0 : ℂ) R)), MemLp (fun ω => g ω y) 2 P :=
    ae_restrict_of_ae (ae_of_all _ fun y => memLp_of_ae_circle h hε hg y)
  have hAint : IntegrableOn (fun y => ∫ ω, (g ω y) ^ 2 ∂P) (closedBall (0 : ℂ) R) := by
    have hm : Measurable fun y => ∫ ω, (g ω y) ^ 2 ∂P := by
      have hm2 : Measurable fun q : ℂ × Ω => g q.2 q.1 ^ 2 := (hgm.comp measurable_swap).pow_const 2
      exact (hm2.stronglyMeasurable.integral_prod_right (ν := P)).measurable
    refine Measure.integrableOn_of_bounded (M := 2 * Real.log (max (R + ε) 1) - Real.log ε)
      measure_closedBall_lt_top.ne hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with y hy
    have heq : ∫ ω, g ω y ^ 2 ∂P = ∫ ω, hcirc ω ε y ^ 2 ∂P :=
      integral_congr_ae (hg.mono fun ω hω => by beta_reduce; rw [hω y])
    rw [Real.norm_of_nonneg (integral_nonneg fun ω => sq_nonneg _), heq]
    exact integral_sq_circle_le h hε (mem_closedBall_zero_iff.1 hy)
  exact integral_mul_integral_swap hgm hX hφ hgR hAL2 hAint

/-- The weighted second moment `ω ↦ ∫ |φ(z)| g(ω,z)² dz` is integrable: Fubini on `P ⊗ dz` (`integrable_prod_iff'`),
with `E[g(z)²] ≤ 2 log max(R+ε,1) - log ε` on the support of `φ`. -/
lemma integrable_weighted_sq [IsProbabilityMeasure P] (h : IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε)
    {g : Ω → ℂ → ℝ} (hgm : Measurable fun p : Ω × ℂ => g p.1 p.2)
    (hg : ∀ᵐ ω ∂P, ∀ z, g ω z = hcirc ω ε z) {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) {R : ℝ}
    (hgR : ∀ z, φ z ≠ 0 → ‖z‖ ≤ R) :
    Integrable (fun ω => ∫ z, |φ z| * g ω z ^ 2) P := by
  have hφc : Continuous φ := hφ.1.continuous
  have hHm : Measurable fun p : Ω × ℂ => |φ p.2| * g p.1 p.2 ^ 2 :=
    (continuous_abs.measurable.comp (hφc.measurable.comp measurable_snd)).mul (hgm.pow_const 2)
  have hHint : Integrable (fun p : Ω × ℂ => |φ p.2| * g p.1 p.2 ^ 2) (P.prod volume) := by
    rw [integrable_prod_iff' hHm.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun z => ?_, ?_⟩
    · exact ((memLp_of_ae_circle h hε hg z).integrable_sq).const_mul |φ z|
    · have hM : ∀ z, ∫ ω, ‖|φ z| * g ω z ^ 2‖ ∂P ≤ (2 * Real.log (max (R + ε) 1) - Real.log ε) * |φ z| := by
        intro z
        by_cases hz : φ z = 0
        · simp [hz]
        · have heq : ∫ ω, g ω z ^ 2 ∂P = ∫ ω, hcirc ω ε z ^ 2 ∂P :=
            integral_congr_ae (hg.mono fun ω hω => by beta_reduce; rw [hω z])
          have hsq : ∫ ω, g ω z ^ 2 ∂P ≤ 2 * Real.log (max (R + ε) 1) - Real.log ε := by
            rw [heq]
            exact integral_sq_circle_le h hε (hgR z hz)
          have hnorm : ∀ ω, ‖|φ z| * g ω z ^ 2‖ = |φ z| * g ω z ^ 2 := fun ω =>
            Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))
          simp only [hnorm]
          rw [integral_const_mul]
          nlinarith [mul_le_mul_of_nonneg_left hsq (abs_nonneg (φ z))]
      have hmeasN : AEStronglyMeasurable (fun z => ∫ ω, ‖|φ z| * g ω z ^ 2‖ ∂P) volume :=
        ((hHm.comp measurable_swap).norm.stronglyMeasurable.integral_prod_right (ν := P)).aestronglyMeasurable
      have hφint : Integrable φ := hφc.integrable_of_hasCompactSupport hφ.2.1
      refine Integrable.mono' ((hφint.abs).const_mul (2 * Real.log (max (R + ε) 1) - Real.log ε)) hmeasN
        (Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun ω => norm_nonneg _)]
      exact hM z
  exact hHint.integral_prod_left

/-- **Pathwise Cauchy-Schwarz** for the weighted integral `∫ φ f` with `f` continuous:
`(∫ φ f)² ≤ (∫ |φ|) (∫ |φ| f²)`. -/
lemma sq_integral_mul_le {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) {f : ℂ → ℝ} (hf : Continuous f) :
    (∫ z, φ z * f z) ^ 2 ≤ (∫ z, |φ z|) * ∫ z, |φ z| * f z ^ 2 := by
  have hφc : Continuous φ := hφ.1.continuous
  have hcs : ∀ k : ℂ → ℝ, Continuous k → Integrable (fun z => |φ z| * k z) := fun k hk =>
    ((continuous_abs.comp hφc).mul hk).integrable_of_hasCompactSupport (hφ.2.1.comp_left abs_zero).mul_right
  have hI1 : Integrable (fun z => |φ z|) := by simpa using hcs 1 continuous_const
  have hI2 : Integrable (fun z => |φ z| * f z ^ 2) := hcs _ (hf.pow 2)
  have hI3 : Integrable (fun z => |φ z| * |f z|) := hcs _ hf.abs
  have ha0 : 0 ≤ ∫ z, |φ z| := integral_nonneg fun z => abs_nonneg _
  have hb0 : 0 ≤ ∫ z, |φ z| * f z ^ 2 := integral_nonneg fun z => mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have hc0 : 0 ≤ ∫ z, |φ z| * |f z| := integral_nonneg fun z => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hJc : |∫ z, φ z * f z| ≤ ∫ z, |φ z| * |f z| := by
    refine abs_integral_le_integral_abs.trans (le_of_eq ?_)
    simp only [abs_mul]
  have hdisc : ∀ t : ℝ, 0 < t →
      2 * (∫ z, |φ z| * |f z|) * t ≤ t ^ 2 * (∫ z, |φ z|) + ∫ z, |φ z| * f z ^ 2 := by
    intro t _
    have hpt : ∀ z, 2 * t * (|φ z| * |f z|) ≤ t ^ 2 * |φ z| + |φ z| * f z ^ 2 := by
      intro z
      have h0 : 0 ≤ |φ z| * (t - |f z|) ^ 2 := mul_nonneg (abs_nonneg _) (sq_nonneg _)
      have e : |φ z| * (t - |f z|) ^ 2 = t ^ 2 * |φ z| - 2 * t * (|φ z| * |f z|) + |φ z| * f z ^ 2 := by
        rw [← sq_abs (f z)]
        ring
      linarith
    have hI4 : Integrable (fun z => t ^ 2 * |φ z| + |φ z| * f z ^ 2) := (hI1.const_mul (t ^ 2)).add hI2
    have hint := integral_mono (hI3.const_mul (2 * t)) hI4 hpt
    rw [integral_const_mul, integral_add (hI1.const_mul _) hI2, integral_const_mul] at hint
    linarith
  have hc2 := sq_le_mul_of_forall_two_mul_le ha0 hb0 hc0 hdisc
  have hsq : (∫ z, φ z * f z) ^ 2 ≤ (∫ z, |φ z| * |f z|) ^ 2 := by
    have h0 := mul_self_le_mul_self (abs_nonneg (∫ z, φ z * f z)) hJc
    nlinarith [sq_abs (∫ z, φ z * f z)]
  linarith [hsq, hc2]

/-- **`L²` bound for the smeared circle average**: `J ω := ∫ φ(z) g(ω,z) dz` is square integrable,
by the pathwise Cauchy-Schwarz inequality and the integrability of `ω ↦ ∫ |φ| g²`. -/
lemma memLp_smear_integral [IsProbabilityMeasure P] (h : IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε)
    {g : Ω → ℂ → ℝ} (hgm : Measurable fun p : Ω × ℂ => g p.1 p.2) (hgc : ∀ ω, Continuous fun z => g ω z)
    (hg : ∀ᵐ ω ∂P, ∀ z, g ω z = hcirc ω ε z) {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    MemLp (fun ω => ∫ z, φ z * g ω z) 2 P := by
  obtain ⟨R, hR⟩ := hφ.2.1.isCompact.isBounded.subset_closedBall (0 : ℂ)
  have hgR : ∀ z, φ z ≠ 0 → ‖z‖ ≤ R := fun z hz =>
    mem_closedBall_zero_iff.1 (hR (subset_tsupport φ (Function.mem_support.2 hz)))
  have hb := integrable_weighted_sq h hε hgm hg hφ hgR
  have hJm : AEStronglyMeasurable (fun ω => ∫ z, φ z * g ω z) P :=
    (((hφ.1.continuous.measurable.comp measurable_snd).mul hgm).stronglyMeasurable.integral_prod_right
      (ν := volume)).aestronglyMeasurable
  have hint : Integrable (fun ω => (∫ z, φ z * g ω z) ^ 2) P :=
    Integrable.mono' (hb.const_mul (∫ z, |φ z|)) (hJm.pow 2)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact sq_integral_mul_le hφ (hgc ω))
  exact (memLp_two_iff_integrable_sq hJm).2 hint

/-- The circle kernel `K_ε φ = circleKernel φ ε` of a test function is a test function (its support lies in
`closedBall 0 (R + ε)`, `R` a radius of `tsupport φ`). -/
lemma isTestFunction_circleKernel {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) {ε : ℝ} (hε : 0 ≤ ε) :
    IsTestFunction univ (circleKernel φ ε) := by
  obtain ⟨R, hR⟩ := hφ.2.1.isCompact.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨circleKernel_contDiff250 hφ ε,
    HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (R + ε)) ?_, Set.subset_univ _⟩
  intro x hx
  have hφz : ∀ θ : ℝ, φ (x - circleMap 0 ε θ) = 0 := by
    intro θ
    refine image_eq_zero_of_notMem_tsupport fun hmem => hx ?_
    have h1 := mem_closedBall_zero_iff.1 (hR hmem)
    rw [mem_closedBall_zero_iff]
    have h2 : ‖x‖ ≤ ‖x - circleMap 0 ε θ‖ + ‖circleMap 0 ε θ‖ := by
      simpa using norm_add_le (x - circleMap 0 ε θ) (circleMap 0 ε θ)
    rw [norm_circleMap_zero_eq hε] at h2
    linarith
  simp [circleKernel, hφz]

/-- **The circle-smear identity** (Duplantier-Sheffield 2011 §3.1). For a whole-plane GFF
`h`, a test function `φ` and `0 < ε ≤ 1`, almost surely `∫ φ(z) h_ε(z) dz = (h, K_ε φ)` with `K_ε φ = circleKernel φ ε`.
Proof (L²): with `J := ∫ φ g`, `Y := hC(K_ε φ)` and `Z := J - Y`, `E[Z·g(z)] = 0` for every `z` (second adjoint
`integral_mul_circleAverage_circleAverage_eq`), hence `E[Z·J] = 0`; `E[Z·Y] = 0` (first adjoint `adjoint_potential`);
so `E[Z²] = 0` and `Z = 0` a.s. -/
theorem circleSmear_ae_eq [IsProbabilityMeasure P] (h : IsWholePlaneGFF P hC hcirc) {φ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    CircleSmearIdentity P hC hcirc φ ε := by
  unfold CircleSmearIdentity
  obtain ⟨g, hgm, hgc, hg⟩ := exists_measurable_circle h hε
  have hψ : IsTestFunction univ (circleKernel φ ε) := isTestFunction_circleKernel hφ hε.le
  have hJ : MemLp (fun ω => ∫ z, φ z * g ω z) 2 P := memLp_smear_integral h hε hgm hgc hg hφ
  have hY : MemLp (fun ω => hC ω (circleKernel φ ε)) 2 P := memLp_pairing h hψ
  have hZ : MemLp (fun ω => (∫ z, φ z * g ω z) - hC ω (circleKernel φ ε)) 2 P := hJ.sub hY
  -- the pointwise identity `g(z) = hcirc(z)` used under the integral in `z`
  have hz : ∀ z, ∫ ω, hC ω (circleKernel φ ε) * g ω z ∂P =
      Real.circleAverage (fun x => ∫ y, circleKernel φ ε y * wholePlaneCov x y) z ε := by
    intro z
    rw [← integral_mul_circle_pairing h hψ hε z]
    exact integral_congr_ae (hg.mono fun ω hω => by beta_reduce; rw [hω z]; ring)
  -- E1: E[Y · J] = E[Y²]
  have E1 : ∫ ω, hC ω (circleKernel φ ε) * (∫ z, φ z * g ω z) ∂P =
      ∫ ω, hC ω (circleKernel φ ε) * hC ω (circleKernel φ ε) ∂P := by
    have hs : ∫ ω, hC ω (circleKernel φ ε) * (∫ z, φ z * g ω z) ∂P =
        ∫ z, φ z * ∫ ω, hC ω (circleKernel φ ε) * g ω z ∂P :=
      integral_mul_smear_swap h hε hgm hg hφ hY
    rw [hs, integral_mul_pairing h hψ hψ, ← adjoint_potential hφ hε hε1 hψ]
    exact integral_congr_ae (Eventually.of_forall fun z => by beta_reduce; rw [hz z])
  -- E2: E[g(z) · J] = E[g(z) · Y] for every z
  have E2 : ∀ z, ∫ ω, g ω z * (∫ z', φ z' * g ω z') ∂P = ∫ ω, g ω z * hC ω (circleKernel φ ε) ∂P := by
    intro z
    have hgz := memLp_of_ae_circle h hε hg z
    have hs : ∫ ω, g ω z * (∫ z', φ z' * g ω z') ∂P =
        ∫ y, φ y * ∫ ω, g ω z * g ω y ∂P :=
      integral_mul_smear_swap h hε hgm hg hφ hgz
    have hc : ∀ y, ∫ ω, g ω z * g ω y ∂P = Real.circleAverage (fun x => Real.circleAverage
        (fun u => wholePlaneCov x u) y ε) z ε := by
      intro y
      have e : ∫ ω, g ω z * g ω y ∂P = ∫ ω, hcirc ω ε z * hcirc ω ε y ∂P :=
        integral_congr_ae (hg.mono fun ω hω => by beta_reduce; rw [hω z, hω y])
      rw [e]
      exact integral_mul_circle_circle h hε z y
    have e2 : ∫ y, φ y * ∫ ω, g ω z * g ω y ∂P = ∫ w, φ w * Real.circleAverage (fun x =>
        Real.circleAverage (fun u => wholePlaneCov x u) w ε) z ε :=
      integral_congr_ae (Eventually.of_forall fun y => by beta_reduce; rw [hc y])
    have e3 : ∫ ω, g ω z * hC ω (circleKernel φ ε) ∂P = ∫ ω, hcirc ω ε z * hC ω (circleKernel φ ε) ∂P :=
      integral_congr_ae (hg.mono fun ω hω => by beta_reduce; rw [hω z])
    rw [hs, e2, integral_mul_circleAverage_circleAverage_eq hφ hε hε1 z, e3,
      integral_mul_circle_pairing h hψ hε z]
  -- E3: E[Z · J] = 0, through `E[Z · g(z)] = 0` for every `z`
  have E3 : ∫ ω, ((∫ z, φ z * g ω z) - hC ω (circleKernel φ ε)) * (∫ z, φ z * g ω z) ∂P = 0 := by
    have hs : ∫ ω, ((∫ z, φ z * g ω z) - hC ω (circleKernel φ ε)) * (∫ z, φ z * g ω z) ∂P =
        ∫ z, φ z * ∫ ω, ((∫ z', φ z' * g ω z') - hC ω (circleKernel φ ε)) * g ω z ∂P :=
      integral_mul_smear_swap h hε hgm hg hφ hZ
    have hzero : ∀ z, ∫ ω, ((∫ z', φ z' * g ω z') - hC ω (circleKernel φ ε)) * g ω z ∂P = 0 := by
      intro z
      have hgz := memLp_of_ae_circle h hε hg z
      have i1 : Integrable (fun ω => g ω z * (∫ z', φ z' * g ω z')) P := hgz.integrable_mul hJ
      have i2 : Integrable (fun ω => g ω z * hC ω (circleKernel φ ε)) P := hgz.integrable_mul hY
      calc ∫ ω, ((∫ z', φ z' * g ω z') - hC ω (circleKernel φ ε)) * g ω z ∂P
          = ∫ ω, (g ω z * (∫ z', φ z' * g ω z') - g ω z * hC ω (circleKernel φ ε)) ∂P :=
            integral_congr_ae (Eventually.of_forall fun ω => by ring)
        _ = ∫ ω, g ω z * (∫ z', φ z' * g ω z') ∂P - ∫ ω, g ω z * hC ω (circleKernel φ ε) ∂P :=
            integral_sub i1 i2
        _ = 0 := by rw [E2 z, sub_self]
    rw [hs]
    simp only [hzero, mul_zero, integral_zero]
  -- E4: E[Z · Y] = 0 (first adjoint)
  have E4 : ∫ ω, ((∫ z, φ z * g ω z) - hC ω (circleKernel φ ε)) * hC ω (circleKernel φ ε) ∂P = 0 := by
    have i1 : Integrable (fun ω => hC ω (circleKernel φ ε) * (∫ z, φ z * g ω z)) P := hY.integrable_mul hJ
    have i2 : Integrable (fun ω => hC ω (circleKernel φ ε) * hC ω (circleKernel φ ε)) P := hY.integrable_mul hY
    calc ∫ ω, ((∫ z, φ z * g ω z) - hC ω (circleKernel φ ε)) * hC ω (circleKernel φ ε) ∂P
        = ∫ ω, (hC ω (circleKernel φ ε) * (∫ z, φ z * g ω z) -
            hC ω (circleKernel φ ε) * hC ω (circleKernel φ ε)) ∂P :=
          integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = ∫ ω, hC ω (circleKernel φ ε) * (∫ z, φ z * g ω z) ∂P -
          ∫ ω, hC ω (circleKernel φ ε) * hC ω (circleKernel φ ε) ∂P := integral_sub i1 i2
      _ = 0 := by rw [E1, sub_self]
  -- E5: E[Z²] = E[Z·J] - E[Z·Y] = 0, hence Z = 0 a.s.
  have hZ2 : ∫ ω, ((∫ z, φ z * g ω z) - hC ω (circleKernel φ ε)) ^ 2 ∂P = 0 := by
    have i3 : Integrable (fun ω => ((∫ z, φ z * g ω z) - hC ω (circleKernel φ ε)) * (∫ z, φ z * g ω z)) P :=
      hZ.integrable_mul hJ
    have i4 : Integrable (fun ω => ((∫ z, φ z * g ω z) - hC ω (circleKernel φ ε)) *
        hC ω (circleKernel φ ε)) P := hZ.integrable_mul hY
    calc ∫ ω, ((∫ z, φ z * g ω z) - hC ω (circleKernel φ ε)) ^ 2 ∂P
        = ∫ ω, (((∫ z, φ z * g ω z) - hC ω (circleKernel φ ε)) * (∫ z, φ z * g ω z) -
            ((∫ z, φ z * g ω z) - hC ω (circleKernel φ ε)) * hC ω (circleKernel φ ε)) ∂P :=
          integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = ∫ ω, ((∫ z, φ z * g ω z) - hC ω (circleKernel φ ε)) * (∫ z, φ z * g ω z) ∂P -
          ∫ ω, ((∫ z, φ z * g ω z) - hC ω (circleKernel φ ε)) * hC ω (circleKernel φ ε) ∂P :=
          integral_sub i3 i4
      _ = 0 := by rw [E3, E4, sub_self]
  have hZ0 := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hZ.integrable_sq).1 hZ2
  -- conclusion: almost surely `J = Y`, and `J = ∫ φ hcirc` since `g = hcirc` a.s.
  filter_upwards [hZ0, hg] with ω hω1 hω2
  have h1 : (∫ z, φ z * g ω z) - hC ω (circleKernel φ ε) = 0 := pow_eq_zero_iff two_ne_zero |>.1 hω1
  have hf : (fun z => φ z * hcirc ω ε z) = fun z => φ z * g ω z := funext fun z => by rw [hω2 z]
  rw [hf]
  linarith

end MatedCRT.LQGMeasure
