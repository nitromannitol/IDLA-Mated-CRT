import HarmonicBalls.Defs.GFF
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.DiscreteSubset
import MatedCRT.LPStaging.Analysis.CircleLogIntegrals

/-!
# The whole-plane covariance kernel under real affine maps

For `r > 0` and `z ∈ ℂ` let `T x = r x + z`. The whole-plane covariance kernel
`G x y = wholePlaneCov x y = log (max |x| 1 · max |y| 1 / |x - y|)` of Harmonic Balls satisfies, for
`A₀(u) = avg_{w ∈ ∂B_r(z)} G(u, w)` and `B₀ = avg_{u ∈ ∂B_r(z)} A₀(u)`, the kernel identity

  `G (T x) (T y) = G x y + A₀ (T x) + A₀ (T y) - B₀`   (`x ≠ y`).

This is the reason why `h ↦ h (r · + z) - h_r(z)` preserves the whole-plane covariance (Duplantier-Sheffield
2011, Section 3.1, eq:gff-scaling; Harmonic-Balls `WholePlaneGFFAffineInvariance`). The proof uses the mean value
property of `log` on circles (Mathlib `circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`).

This file proves the analytic lemmas: the kernel formula, the closed forms of `A₀` and `B₀`, the scaling of circle
averages, the change of variables on `ℂ`, and the kernel identity.
-/

namespace MatedCRT.Field

open MeasureTheory Filter Set Metric

/-- The whole-plane kernel off the diagonal: `G x y = -log|x - y| + log max(|x|,1) + log max(|y|,1)`. -/
theorem wholePlaneCov_of_ne {x y : ℂ} (hxy : x ≠ y) :
    HarmonicBalls.wholePlaneCov x y =
      -Real.log ‖x - y‖ + Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1) := by
  unfold HarmonicBalls.wholePlaneCov
  have h1 : (0 : ℝ) < max ‖x‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have h2 : (0 : ℝ) < max ‖y‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have h3 : (0 : ℝ) < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  rw [Real.log_div (mul_pos h1 h2).ne' h3.ne', Real.log_mul h1.ne' h2.ne']
  ring

/-- `log⁺ |x| = log max(|x|, 1)`. -/
theorem posLog_norm_eq_log_max (x : ℂ) : Real.posLog ‖x‖ = Real.log (max ‖x‖ 1) :=
  LatticeProb.CircleLogIntegrals.posLog_norm_eq_log_max x

/-- The mean value property of `log |· - u|` on the circle `∂B_r(z)`, `r > 0` (Mathlib). -/
theorem circleAverage_log_norm_eq (z u : ℂ) {r : ℝ} (hr : 0 < r) :
    Real.circleAverage (fun w => Real.log ‖w - u‖) z r =
      Real.log r + Real.posLog (r⁻¹ * ‖z - u‖) :=
  LatticeProb.CircleLogIntegrals.circleAverage_log_norm_eq z u hr

/-- `w ↦ log max(|w|,1)` is continuous. -/
theorem continuous_log_max_norm : Continuous fun w : ℂ => Real.log (max ‖w‖ 1) :=
  LatticeProb.CircleLogIntegrals.continuous_log_max_norm

/-- The codiscrete filter of any set contains the complement of a point. -/
theorem eventually_ne_codiscreteWithin (S : Set ℂ) (u : ℂ) :
    ∀ᶠ w in codiscreteWithin S, w ≠ u :=
  LatticeProb.CircleLogIntegrals.eventually_ne_codiscreteWithin S u

/-- The log-kernel closed form of `A₀(u) = avg_{w ∈ ∂B_r(z)} G(u, w)` for `r > 0`:
`A₀(u) = log max(|u|,1) + F₀ - (log r + log⁺(|z - u|/r))`, where `F₀ = avg_{∂B_r(z)} log max(|w|,1)`. -/
theorem circleAverage_wholePlaneCov_eq (z u : ℂ) {r : ℝ} (hr : 0 < r) :
    Real.circleAverage (fun w => HarmonicBalls.wholePlaneCov u w) z r =
      Real.log (max ‖u‖ 1) + Real.circleAverage (fun w => Real.log (max ‖w‖ 1)) z r
        - (Real.log r + Real.posLog (r⁻¹ * ‖z - u‖)) := by
  have hcongr : (fun w => HarmonicBalls.wholePlaneCov u w) =ᶠ[codiscreteWithin (sphere z |r|)]
      (fun w => (Real.log (max ‖u‖ 1) + Real.log (max ‖w‖ 1)) - Real.log ‖w - u‖) := by
    filter_upwards [eventually_ne_codiscreteWithin (sphere z |r|) u] with w hw
    rw [wholePlaneCov_of_ne (Ne.symm hw), norm_sub_rev]
    ring
  have hI1 : CircleIntegrable (fun w : ℂ => Real.log (max ‖u‖ 1) + Real.log (max ‖w‖ 1)) z r :=
    (continuous_const.add continuous_log_max_norm).continuousOn.circleIntegrable hr.le
  have hI2 : CircleIntegrable (fun w : ℂ => Real.log ‖w - u‖) z r :=
    circleIntegrable_log_norm_sub_const (a := u) (c := z) r
  rw [Real.circleAverage_congr_codiscreteWithin hcongr hr.ne',
    Real.circleAverage_fun_sub hI1 hI2, Real.circleAverage_fun_add
      (continuous_const.continuousOn.circleIntegrable hr.le)
      (continuous_log_max_norm.continuousOn.circleIntegrable hr.le),
    Real.circleAverage_const, circleAverage_log_norm_eq z u hr]

/-- `F₀ z r`: the average of `log max(|w|,1)` over the circle `∂B_r(z)`. -/
noncomputable def F0 (z : ℂ) (r : ℝ) : ℝ := Real.circleAverage (fun w => Real.log (max ‖w‖ 1)) z r

/-- `A₀ z r u = avg_{w ∈ ∂B_r(z)} G(u, w)`, the average of the whole-plane kernel over a circle. -/
noncomputable def A0 (z : ℂ) (r : ℝ) (u : ℂ) : ℝ :=
  Real.circleAverage (fun w => HarmonicBalls.wholePlaneCov u w) z r

/-- `B₀ z r = avg_{u ∈ ∂B_r(z)} A₀ z r u`, the self-covariance of the circle average `h_r(z)`. -/
noncomputable def B0 (z : ℂ) (r : ℝ) : ℝ := Real.circleAverage (fun u => A0 z r u) z r

/-- On the circle `∂B_r(z)` the kernel average has the closed form `A₀ u = log max(|u|,1) + F₀ - log r`. -/
theorem B0_eq {z : ℂ} {r : ℝ} (hr : 0 < r) : B0 z r = 2 * F0 z r - Real.log r := by
  have hEq : EqOn (fun u => A0 z r u)
      (fun u => (Real.log (max ‖u‖ 1) + F0 z r) - Real.log r) (sphere z |r|) := by
    intro u hu
    show A0 z r u = Real.log (max ‖u‖ 1) + F0 z r - Real.log r
    have hn : ‖z - u‖ = r := by
      rw [norm_sub_rev, ← dist_eq_norm, mem_sphere.1 hu, abs_of_pos hr]
    have hA : A0 z r u = Real.log (max ‖u‖ 1) + F0 z r - (Real.log r + Real.posLog (r⁻¹ * ‖z - u‖)) :=
      circleAverage_wholePlaneCov_eq z u hr
    rw [hA, hn, inv_mul_cancel₀ hr.ne']
    have h1 : Real.posLog 1 = 0 := by simp [Real.posLog_def]
    rw [h1]
    ring
  have hJ1 : CircleIntegrable (fun u : ℂ => Real.log (max ‖u‖ 1) + F0 z r) z r :=
    (continuous_log_max_norm.add continuous_const).continuousOn.circleIntegrable hr.le
  have hJ2 : CircleIntegrable (fun _ : ℂ => Real.log r) z r := circleIntegrable_const _ _ _
  unfold B0
  rw [Real.circleAverage_congr_sphere hEq, Real.circleAverage_fun_sub hJ1 hJ2,
    Real.circleAverage_fun_add (continuous_log_max_norm.continuousOn.circleIntegrable hr.le)
      (circleIntegrable_const _ _ _), Real.circleAverage_const, Real.circleAverage_const]
  unfold F0
  ring

/-- **The kernel identity.** For `r > 0`, `x ≠ y`: `G(T x, T y) = G(x, y) + A₀(T x) + A₀(T y) - B₀` with
`T x = r x + z`. -/
theorem wholePlaneCov_affine_eq {x y : ℂ} {r : ℝ} (hr : 0 < r) (z : ℂ) (hxy : x ≠ y) :
    HarmonicBalls.wholePlaneCov (r * x + z) (r * y + z) =
      HarmonicBalls.wholePlaneCov x y + A0 z r (r * x + z) + A0 z r (r * y + z) - B0 z r := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hTxy : (r : ℂ) * x + z ≠ (r : ℂ) * y + z := fun h => hxy (mul_left_cancel₀ hr' (add_right_cancel h))
  have hxy' : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hxy)
  have hn : ‖((r : ℂ) * x + z) - ((r : ℂ) * y + z)‖ = r * ‖x - y‖ := by
    rw [show ((r : ℂ) * x + z) - ((r : ℂ) * y + z) = (r : ℂ) * (x - y) by ring, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hzx : r⁻¹ * ‖z - ((r : ℂ) * x + z)‖ = ‖x‖ := by
    rw [show z - ((r : ℂ) * x + z) = -((r : ℂ) * x) by ring, norm_neg, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hr.le]
    field_simp
  have hzy : r⁻¹ * ‖z - ((r : ℂ) * y + z)‖ = ‖y‖ := by
    rw [show z - ((r : ℂ) * y + z) = -((r : ℂ) * y) by ring, norm_neg, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hr.le]
    field_simp
  rw [wholePlaneCov_of_ne hTxy, hn, Real.log_mul hr.ne' hxy', wholePlaneCov_of_ne hxy]
  unfold A0
  rw [circleAverage_wholePlaneCov_eq z _ hr, circleAverage_wholePlaneCov_eq z _ hr, hzx, hzy,
    posLog_norm_eq_log_max, posLog_norm_eq_log_max, B0_eq hr]
  unfold F0
  ring

/-- **Scaling of circle averages.** For `r ∈ ℝ`, `avg_{u ∈ ∂B_s(w)} f (r u + z) = avg_{v ∈ ∂B_{rs}(rw + z)} f v`. -/
theorem circleAverage_affine (f : ℂ → ℝ) (r : ℝ) (z w : ℂ) (s : ℝ) :
    Real.circleAverage (fun u => f (r * u + z)) w s = Real.circleAverage f (r * w + z) (r * s) :=
  LatticeProb.CircleLogIntegrals.circleAverage_affine f r z w s

/-- **Change of variables on `ℂ`.** For `r > 0`: `∫ u, F u = r² ∫ x, F (r x + z)`. -/
theorem integral_affine_change (F : ℂ → ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∫ u, F u = r ^ 2 * ∫ x, F ((r : ℂ) * x + z) :=
  LatticeProb.CircleLogIntegrals.integral_affine_change F hr z

/-- **Change of variables for pairings.** For `r > 0`: `∫ y, φ((y - z)/r) F(y) dy = r² ∫ x, φ(x) F(r x + z) dx`. -/
theorem integral_affine_pullback (φ F : ℂ → ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∫ y, φ ((y - z) / (r : ℂ)) * F y = r ^ 2 * ∫ x, φ x * F ((r : ℂ) * x + z) :=
  LatticeProb.CircleLogIntegrals.integral_affine_pullback φ F hr z

end MatedCRT.Field
