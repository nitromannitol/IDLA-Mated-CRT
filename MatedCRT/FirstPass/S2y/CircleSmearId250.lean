import MatedCRT.FirstPass.S2y.LateralBilin250
import MatedCRT.FirstPass.S2y.CircleKernelSmooth250

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

end MatedCRT.LQGMeasure
