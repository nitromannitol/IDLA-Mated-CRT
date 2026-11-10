import MatedCRT.FirstPass.S2y.LateralBilin250
import MatedCRT.FirstPass.S2y.CircleKernelSmooth250
import MatedCRT.FirstPass.S2y.LateralHc250

/-!
# The circle-smear identity of the whole-plane field (fp-S2y-circle-smear-id, q1; chat 250 §1.2, z8 step R3)

For a test function `φ` and a radius `ε > 0`, the smeared circle average `∫ φ(z) h_ε(z) dz` of a whole-plane GFF equals
the pairing `(h, K_ε φ)` with the circle kernel `K_ε φ = circleKernel φ ε`, almost surely (Duplantier-Sheffield 2011,
Section 3.1; Armitage-Gardiner, Fubini for the adjoint of the circle average).

The proof is the L² argument of z8's notes: `J := ∫ φ h_ε` is square integrable, and `E[(J - (h, K_ε φ))²] = 0`
by Fubini on the second moments `wholePlaneGFFCov`.

This file contains the covariance identities of circle averages (`integral_mul_circle_circle`,
`integral_mul_circle_pairing`), reduced to `IsWholePlaneGFF.covariance_eq` as in `LateralBilin250.integral_mul_pairing`.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology Real Metric HarmonicBalls
open scoped ENNReal

namespace MatedCRT.LQGMeasure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The a.s. circle-smear identity for the whole-plane field (chat 250 §1.2; z8 step R3): the smeared circle average
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

/-- **Sup bound for the circle averages** (z8 step R3, sub-step 1): for `‖z‖ ≤ R`, the second moment of the circle average
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

/-- **Joint measurability of the circle averages** (step 6 of z8's R3 route). For `ε > 0` there is a jointly measurable
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

end MatedCRT.LQGMeasure
