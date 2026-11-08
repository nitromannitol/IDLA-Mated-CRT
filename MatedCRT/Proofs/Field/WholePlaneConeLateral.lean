import MatedCRT.Proofs.Field.WholePlaneRadialGlobal
import MatedCRT.Proofs.Field.WholePlaneConeRadial

/-!
# The cone's circle averages: radial level functional and decomposition (eq:gff, cone side)

For a cone field and a region circle `o`, `h_r(z) + γ log|z| = L_o + Y_o` almost surely, where `L_o` is the lateral
circle average (`latCirc`) and `Y_o` the Gaussian level integral of the centred radial process (`radial_global_space`).
The level integral is a measurable functional of the radial path (`circLevelFun`), which gives the independence of
`Y_o` and the lateral part from `IsQuantumCone.indep`.
-/

namespace MatedCRT.Field

open MeasureTheory ProbabilityTheory Filter Topology Set Real Metric HarmonicBalls
open MatedCRT.Field.GaussClosure MatedCRT.Field.Level MatedCRT.Field.ConeRadial
open scoped NNReal

/-- The index set of region circles, by radius and centre. -/
abbrev RegIdx := {p : ℝ × ℂ // InLevelRegion p.1 p.2}

/-- The level functional of the circle `o` on a path `p : ℝ≥0 → ℝ` (the first component of the radial process,
`p t = h_{e^{-t}}(0)`), measurable in `p`. -/
noncomputable def circLevelFun (γ : ℝ) (o : RegIdx) : (ℝ≥0 → ℝ) → ℝ :=
  fun p => levelRiemannLim (volume.restrict (Ioc (0 : ℝ) (2 * π))) (fun _ => (2 * π)⁻¹)
    (fun θ => -Real.log ‖circleMap o.1.2 o.1.1 θ‖) (fun u => p (Real.toNNReal u) - γ * max u 0)

lemma measurable_circLevelFun (γ : ℝ) (o : RegIdx) : Measurable (circLevelFun γ o) :=
  (measurable_levelRiemannLim _ _ _).comp (Measurable.of_eval fun u =>
    ((measurable_pi_apply (Real.toNNReal u)).sub measurable_const))

lemma circleAverage_log_norm_center {r : ℝ} {z : ℂ} (hr : 0 < r) (hzr : r < ‖z‖) :
    Real.circleAverage (fun x => Real.log ‖x‖) z r = Real.log ‖z‖ := by
  have h := circleAverage_log_norm_eq z 0 hr
  simp only [sub_zero] at h
  rw [h]
  have hz : 0 < ‖z‖ := hr.trans hzr
  have h1 : 1 ≤ r⁻¹ * ‖z‖ := by
    rw [← div_eq_inv_mul, one_le_div hr]
    exact hzr.le
  unfold Real.posLog
  rw [max_eq_right (Real.log_nonneg h1), Real.log_mul (inv_ne_zero hr.ne') hz.ne', Real.log_inv]
  ring

/-- The circle average of `-log|x|` over a region circle is `-log|z|`. -/
lemma circleAverage_neg_log_norm_center {r : ℝ} {z : ℂ} (hr : 0 < r) (hzr : r < ‖z‖) :
    Real.circleAverage (fun x => -Real.log ‖x‖) z r = -Real.log ‖z‖ := by
  have hneg : Real.circleAverage (fun x => -Real.log ‖x‖) z r =
      -Real.circleAverage (fun x => Real.log ‖x‖) z r := by
    unfold Real.circleAverage
    simp only [intervalIntegral.integral_neg, smul_eq_mul, mul_neg]
  rw [hneg, circleAverage_log_norm_center hr hzr]

/-- On a region circle, the radial circle average of a sample with continuous centred radial path is the centred
level average minus `γ log|z|`. -/
lemma radAvg_eq_coneRadW {γ : ℝ} {hc : ℝ → ℂ → ℝ} (hcont : Continuous fun u => coneRadW γ hc u) {r : ℝ} {z : ℂ}
    (hreg : InLevelRegion r z) :
    radAvg hc r z = Real.circleAverage (fun x => coneRadW γ hc (-Real.log ‖x‖)) z r - γ * Real.log ‖z‖ := by
  obtain ⟨hr, hzr, hz1⟩ := hreg
  have hreg : InLevelRegion r z := ⟨hr, hzr, hz1⟩
  have hsph : radAvg hc r z = Real.circleAverage
      (fun x => coneRadW γ hc (-Real.log ‖x‖) + γ * (-Real.log ‖x‖)) z r := by
    unfold radAvg
    refine Real.circleAverage_congr_sphere (fun x hx => ?_)
    have hx0 := ne_zero_of_mem_region_sphere hreg hx
    have hnn := neg_log_nonneg_of_mem_sphere hreg hx
    simp only [coneRadW, max_eq_left hnn]
    rw [neg_neg, Real.exp_log (norm_pos_iff.2 hx0)]
    ring
  have hlogS : ContinuousOn (fun x : ℂ => -Real.log ‖x‖) (sphere z |r|) := by
    refine ContinuousOn.neg (ContinuousOn.log continuous_norm.continuousOn (fun x hx => ?_))
    exact norm_ne_zero_iff.2 (ne_zero_of_mem_region_sphere hreg hx)
  rw [abs_of_pos hr] at hlogS
  have hI1 : CircleIntegrable (fun x : ℂ => coneRadW γ hc (-Real.log ‖x‖)) z r :=
    ContinuousOn.circleIntegrable hr.le (hcont.comp_continuousOn hlogS)
  have hI2 : CircleIntegrable (fun x : ℂ => γ * (-Real.log ‖x‖)) z r :=
    ContinuousOn.circleIntegrable hr.le (continuousOn_const.mul hlogS)
  have hc2 : Real.circleAverage (fun x : ℂ => γ * (-Real.log ‖x‖)) z r =
      γ * Real.circleAverage (fun x : ℂ => -Real.log ‖x‖) z r := by
    unfold Real.circleAverage
    simp only [intervalIntegral.integral_const_mul, smul_eq_mul]
    ring
  rw [hsph, circleAverage_fun_add hI1 hI2, hc2, circleAverage_neg_log_norm_center hr hzr]
  ring

/-- The cone's circle average decomposes a.s. as `h_r(z) + γ log|z| = L_o + Y_o`. -/
lemma cone_circle_decomp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hcirc : Ω → ℝ → ℂ → ℝ} {γ : ℝ}
    (o : RegIdx) {Y : Ω → ℝ}
    (hY : ∀ᵐ ω ∂P, Real.circleAverage (fun x => coneRadW γ (hcirc ω) (-Real.log ‖x‖)) o.1.2 o.1.1 = Y ω)
    (hc : ∀ᵐ ω ∂P, Continuous fun u => coneRadW γ (hcirc ω) u) :
    ∀ᵐ ω ∂P, hcirc ω o.1.1 o.1.2 - (-γ * Real.log ‖o.1.2‖) = latCirc (hcirc ω) o.1.1 o.1.2 + Y ω := by
  filter_upwards [hY, hc] with ω hω hcω
  have h := radAvg_eq_coneRadW hcω o.2
  unfold latCirc
  rw [h, hω]
  ring

/-- The measurable level functional of the path is a.s. the Gaussian level integral `Y_o`. -/
lemma circLevelFun_ae_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hcirc : Ω → ℝ → ℂ → ℝ} {γ : ℝ}
    (o : RegIdx) {Y : Ω → ℝ}
    (hY : ∀ᵐ ω ∂P, Real.circleAverage (fun x => coneRadW γ (hcirc ω) (-Real.log ‖x‖)) o.1.2 o.1.1 = Y ω)
    (hc : ∀ᵐ ω ∂P, Continuous fun u => coneRadW γ (hcirc ω) u) :
    ∀ᵐ ω ∂P, circLevelFun γ o (fun t : ℝ≥0 => hcirc ω (Real.exp (-(t : ℝ))) 0) = Y ω := by
  filter_upwards [hY, hc] with ω hω hcω
  obtain ⟨hr, hzr, hz1⟩ := o.2
  have hpath : (fun u : ℝ => (fun t : ℝ≥0 => hcirc ω (Real.exp (-(t : ℝ))) 0) (Real.toNNReal u) - γ * max u 0)
      = fun u => coneRadW γ (hcirc ω) u := by
    funext u
    simp only [coneRadW, Real.coe_toNNReal']
  have hsc := continuous_neg_log_circleMap hr o.1.2 hzr
  have hint : Integrable (fun θ : ℝ => (fun _ : ℝ => (2 * π)⁻¹) θ *
      (fun u : ℝ => coneRadW γ (hcirc ω) u) (-Real.log ‖circleMap o.1.2 o.1.1 θ‖))
      (volume.restrict (Ioc (0 : ℝ) (2 * π))) := by
    have hc' : Continuous fun θ : ℝ => (2 * π)⁻¹ * coneRadW γ (hcirc ω) (-Real.log ‖circleMap o.1.2 o.1.1 θ‖) :=
      continuous_const.mul (hcω.comp hsc)
    exact (hc'.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  simp only [circLevelFun]
  rw [hpath, levelRiemannLim_eq_levelIntegral hsc.measurable (integrable_const _) hcω hint,
    ← circleAverage_neg_log_eq_levelIntegral (fun u => coneRadW γ (hcirc ω) u) hr o.1.2 hzr]
  exact hω

end MatedCRT.Field
