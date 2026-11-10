import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.Support

/-!
# Approximate identity for circle averages (chat 240, §2.2; fp-S2y-lateral-240, z8)

For a measurable, locally integrable `a : ℂ → ℝ` and a test function `φ`, the pairing of `φ` with the
circle averages of `a` converges to the pairing with `a` as the radius tends to `0`:
`∫ φ(z) · circleAverage a z ε dz → ∫ φ a` (Armitage-Gardiner, approximate identity for the circle means).
The proof is Fubini on `ℂ × [0, 2π]` and dominated convergence for the adjoint kernel
`circleKernel φ ε x = (2π)⁻¹ ∫₀^{2π} φ(x - ε e^{iθ}) dθ`, which tends to `φ(x)` uniformly.
-/

open MeasureTheory Filter Topology Set Metric Complex
open scoped Real

namespace MatedCRT.LQGMeasure

/-- The adjoint kernel of the circle average: `K_ε φ(x) = (2π)⁻¹ ∫₀^{2π} φ(x - ε e^{iθ}) dθ`. -/
noncomputable def circleKernel (φ : ℂ → ℝ) (ε : ℝ) (x : ℂ) : ℝ :=
  (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, φ (x - circleMap 0 ε θ)

lemma circleMap_eq_add_zero (z : ℂ) (ε θ : ℝ) : circleMap z ε θ = z + circleMap 0 ε θ := by
  simp [circleMap]

lemma norm_circleMap_zero_eq {ε : ℝ} (hε : 0 ≤ ε) (θ : ℝ) : ‖circleMap 0 ε θ‖ = ε := by
  rw [norm_circleMap_zero, abs_of_nonneg hε]

/-- Integrability of `(z, θ) ↦ A (z + ε e^{iθ})` on `ℂ × [0, 2π]` for an integrable `A`. -/
lemma integrable_shear_prod {A : ℂ → ℝ} (hA : Integrable A) (hAm : Measurable A) (ε : ℝ) :
    Integrable (fun p : ℂ × ℝ => A (p.1 + circleMap 0 ε p.2))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) (2 * π)))) := by
  have hc : Measurable fun p : ℂ × ℝ => p.1 + circleMap 0 ε p.2 :=
    measurable_fst.add ((continuous_circleMap 0 ε).measurable.comp measurable_snd)
  refine (integrable_prod_iff' (hAm.comp hc).aestronglyMeasurable).2 ⟨?_, ?_⟩
  · exact Eventually.of_forall fun θ => by
      show Integrable (fun x => A (x + circleMap 0 ε θ)) volume
      exact hA.comp_add_right _
  · exact (integrable_const (∫ z, ‖A z‖)).congr (Eventually.of_forall fun θ =>
      (integral_add_right_eq_self (fun z => ‖A z‖) (circleMap 0 ε θ)).symm)

/-- The indicator of the closed ball of radius `R` of `‖a‖` is integrable when `a` is locally integrable. -/
lemma integrable_indicator_norm {a : ℂ → ℝ} (hloc : LocallyIntegrable a volume) (R : ℝ) :
    Integrable ((closedBall (0 : ℂ) R).indicator fun x => ‖a x‖) := by
  rw [integrable_indicator_iff measurableSet_closedBall]
  exact (hloc.integrableOn_isCompact (isCompact_closedBall (0 : ℂ) R)).norm

/-- **Approximate identity for circle averages** (chat 240, §2.2). For `ε ∈ (0, 1]`, the pairing of `φ`
with the circle average of `a` at radius `ε` equals the pairing of `a` with the adjoint kernel. -/
theorem integral_mul_circleAverage_eq {a φ : ℂ → ℝ} (ha : Measurable a)
    (hloc : LocallyIntegrable a volume) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ z, φ z * Real.circleAverage a z ε = ∫ x, a x * circleKernel φ ε x := by
  obtain ⟨R0, hR0⟩ := hφc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨M, hM⟩ := hφ.bounded_above_of_compact_support hφc
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hφ0 : ∀ x : ℂ, R0 < ‖x‖ → φ x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxt
    have h := hR0 hxt
    rw [mem_closedBall_zero_iff] at h
    linarith
  set A : ℂ → ℝ := (closedBall (0 : ℂ) (R0 + 1)).indicator fun x => ‖a x‖ with hA_def
  have hAint : Integrable A := integrable_indicator_norm hloc (R0 + 1)
  have hAm : Measurable A := (ha.norm).indicator measurableSet_closedBall
  have hA0 : ∀ x, 0 ≤ A x := fun x => indicator_nonneg (fun y _ => norm_nonneg _) x
  have hcε : ∀ θ : ℝ, ‖circleMap 0 ε θ‖ = ε := fun θ => norm_circleMap_zero_eq hε.le θ
  have hcm : Measurable fun θ : ℝ => circleMap 0 ε θ := (continuous_circleMap 0 ε).measurable
  -- the two Fubini integrands are integrable
  have hI1 : Integrable (fun p : ℂ × ℝ => φ p.1 * a (p.1 + circleMap 0 ε p.2))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) (2 * π)))) := by
    refine Integrable.mono' ((integrable_shear_prod hAint hAm ε).const_mul M)
      ((hφ.measurable.comp measurable_fst |>.mul
        (ha.comp (measurable_fst.add (hcm.comp measurable_snd)))).aestronglyMeasurable) ?_
    refine Eventually.of_forall fun p => ?_
    by_cases h : p.1 ∈ closedBall (0 : ℂ) R0
    · have hmem : p.1 + circleMap 0 ε p.2 ∈ closedBall (0 : ℂ) (R0 + 1) := by
        rw [mem_closedBall_zero_iff] at h ⊢
        have := norm_add_le p.1 (circleMap 0 ε p.2)
        rw [hcε] at this
        linarith
      rw [norm_mul, hA_def, indicator_of_mem hmem]
      exact mul_le_mul_of_nonneg_right (hM p.1) (norm_nonneg _)
    · rw [mem_closedBall_zero_iff, not_le] at h
      rw [hφ0 p.1 h, zero_mul, norm_zero]
      exact mul_nonneg hM0 (hA0 _)
  have hI2 : Integrable (fun p : ℝ × ℂ => φ (p.2 - circleMap 0 ε p.1) * a p.2)
      ((volume.restrict (Ioc (0 : ℝ) (2 * π))).prod volume) := by
    have hg : Integrable (fun p : ℝ × ℂ => M * A p.2)
        ((volume.restrict (Ioc (0 : ℝ) (2 * π))).prod volume) := by
      exact (hAint.comp_snd (volume.restrict (Ioc (0 : ℝ) (2 * π)))).const_mul M
    refine Integrable.mono' hg
      ((hφ.measurable.comp (measurable_snd.sub (hcm.comp measurable_fst)) |>.mul
        (ha.comp measurable_snd)).aestronglyMeasurable) ?_
    refine Eventually.of_forall fun p => ?_
    by_cases h : p.2 - circleMap 0 ε p.1 ∈ closedBall (0 : ℂ) R0
    · have hmem : p.2 ∈ closedBall (0 : ℂ) (R0 + 1) := by
        rw [mem_closedBall_zero_iff] at h ⊢
        have h2 : p.2 = (p.2 - circleMap 0 ε p.1) + circleMap 0 ε p.1 := (sub_add_cancel _ _).symm
        have := norm_add_le (p.2 - circleMap 0 ε p.1) (circleMap 0 ε p.1)
        rw [← h2, hcε] at this
        linarith
      rw [norm_mul, hA_def, indicator_of_mem hmem]
      exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
    · rw [mem_closedBall_zero_iff, not_le] at h
      rw [hφ0 _ h, zero_mul, norm_zero]
      exact mul_nonneg hM0 (hA0 _)
  -- the Fubini swaps
  have hsw1 : ∫ z, ∫ θ in Ioc (0 : ℝ) (2 * π), φ z * a (z + circleMap 0 ε θ) =
      ∫ θ in Ioc (0 : ℝ) (2 * π), ∫ z, φ z * a (z + circleMap 0 ε θ) :=
    integral_integral_swap (f := fun z θ => φ z * a (z + circleMap 0 ε θ)) hI1
  have hper : ∀ θ : ℝ, ∫ z, φ z * a (z + circleMap 0 ε θ) = ∫ x, φ (x - circleMap 0 ε θ) * a x := by
    intro θ
    have := integral_add_right_eq_self (μ := volume) (fun z => φ (z - circleMap 0 ε θ) * a z)
      (circleMap 0 ε θ)
    simp only [add_sub_cancel_right] at this
    exact this
  have hsw2 : ∫ θ in Ioc (0 : ℝ) (2 * π), ∫ x, φ (x - circleMap 0 ε θ) * a x =
      ∫ x, ∫ θ in Ioc (0 : ℝ) (2 * π), φ (x - circleMap 0 ε θ) * a x :=
    integral_integral_swap (f := fun θ x => φ (x - circleMap 0 ε θ) * a x) hI2
  have hz : ∀ z : ℂ, φ z * Real.circleAverage a z ε =
      (2 * π)⁻¹ * ∫ θ in Ioc (0 : ℝ) (2 * π), φ z * a (z + circleMap 0 ε θ) := by
    intro z
    rw [Real.circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le (by positivity)]
    simp only [circleMap_eq_add_zero z ε]
    rw [integral_const_mul (φ z)]
    ring
  calc ∫ z, φ z * Real.circleAverage a z ε
      = ∫ z, (2 * π)⁻¹ * ∫ θ in Ioc (0 : ℝ) (2 * π), φ z * a (z + circleMap 0 ε θ) :=
        integral_congr_ae (Eventually.of_forall hz)
    _ = (2 * π)⁻¹ * ∫ z, ∫ θ in Ioc (0 : ℝ) (2 * π), φ z * a (z + circleMap 0 ε θ) :=
        integral_const_mul _ _
    _ = (2 * π)⁻¹ * ∫ θ in Ioc (0 : ℝ) (2 * π), ∫ z, φ z * a (z + circleMap 0 ε θ) := by
        rw [hsw1]
    _ = (2 * π)⁻¹ * ∫ θ in Ioc (0 : ℝ) (2 * π), ∫ x, φ (x - circleMap 0 ε θ) * a x := by
        simp only [hper]
    _ = (2 * π)⁻¹ * ∫ x, ∫ θ in Ioc (0 : ℝ) (2 * π), φ (x - circleMap 0 ε θ) * a x := by
        rw [hsw2]
    _ = ∫ x, a x * circleKernel φ ε x := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [circleKernel]
        rw [intervalIntegral.integral_of_le (by positivity), integral_mul_const]
        ring

/-- The adjoint kernel tends to the test function pointwise as the radius tends to `0` (uniform continuity). -/
lemma tendsto_circleKernel {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) (x : ℂ) :
    Tendsto (fun ε => circleKernel φ ε x) (𝓝[>] 0) (𝓝 (φ x)) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨η, hη, hηφ⟩ := Metric.uniformContinuous_iff.1
    (hφc.uniformContinuous_of_continuous hφ) (δ / 2) (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hη] with ε hε
  have hε0 : 0 ≤ ε := hε.1.le
  have hbound : ∀ θ ∈ Set.uIoc (0 : ℝ) (2 * π), ‖φ (x - circleMap 0 ε θ) - φ x‖ ≤ δ / 2 := by
    intro θ _
    have hd : dist (x - circleMap 0 ε θ) x < η := by
      rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_circleMap_zero_eq hε0 θ]
      exact hε.2
    have := hηφ hd
    rw [dist_eq_norm] at this
    exact this.le
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hc : Continuous fun θ : ℝ => φ (x - circleMap 0 ε θ) :=
    hφ.comp (continuous_const.sub (continuous_circleMap 0 ε))
  have hsub : circleKernel φ ε x - φ x =
      (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, (φ (x - circleMap 0 ε θ) - φ x) := by
    unfold circleKernel
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
      intervalIntegral.integral_const, smul_eq_mul]
    field_simp
    ring
  rw [Real.dist_eq, hsub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)]
  have h2 : |∫ θ in (0 : ℝ)..2 * π, (φ (x - circleMap 0 ε θ) - φ x)| ≤ δ / 2 * (2 * π) := by
    have := hint
    rwa [Real.norm_eq_abs, sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at this
  calc (2 * π)⁻¹ * |∫ θ in (0 : ℝ)..2 * π, (φ (x - circleMap 0 ε θ) - φ x)|
      ≤ (2 * π)⁻¹ * (δ / 2 * (2 * π)) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = δ / 2 := by field_simp
    _ < δ := by linarith

/-- **Approximate identity for circle averages of a locally integrable function** (chat 240, §2.2). For a
measurable, locally integrable `a` and a test function `φ`, `∫ φ(z) circleAverage a z ε dz → ∫ φ a` as
`ε → 0⁺`: the radial approximate identity used for the radial part of a cone's pairing approximants. -/
theorem tendsto_integral_mul_circleAverage {a φ : ℂ → ℝ} (ha : Measurable a)
    (hloc : LocallyIntegrable a volume) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Tendsto (fun ε : ℝ => ∫ z, φ z * Real.circleAverage a z ε) (𝓝[>] 0) (𝓝 (∫ x, φ x * a x)) := by
  obtain ⟨R0, hR0⟩ := hφc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨M, hM⟩ := hφ.bounded_above_of_compact_support hφc
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hφ0 : ∀ x : ℂ, R0 < ‖x‖ → φ x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxt
    have h := hR0 hxt
    rw [mem_closedBall_zero_iff] at h
    linarith
  set A : ℂ → ℝ := (closedBall (0 : ℂ) (R0 + 1)).indicator fun x => ‖a x‖ with hA_def
  have hAint : Integrable A := integrable_indicator_norm hloc (R0 + 1)
  have hA0 : ∀ x, 0 ≤ A x := fun x => indicator_nonneg (fun y _ => norm_nonneg _) x
  -- pointwise domination of the integrand `a x * K_ε φ x` for `ε ∈ (0, 1]`
  have hKb : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x : ℂ, ‖a x * circleKernel φ ε x‖ ≤ M * A x := by
    intro ε hε hε1 x
    by_cases hx : x ∈ closedBall (0 : ℂ) (R0 + 1)
    · have hKM : ‖circleKernel φ ε x‖ ≤ M := by
        unfold circleKernel
        have hI : ‖∫ θ in (0 : ℝ)..2 * π, φ (x - circleMap 0 ε θ)‖ ≤ M * |2 * π - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => hM _
        rw [norm_mul, norm_inv, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
        rw [sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at hI
        calc (2 * π)⁻¹ * ‖∫ θ in (0 : ℝ)..2 * π, φ (x - circleMap 0 ε θ)‖
            ≤ (2 * π)⁻¹ * (M * (2 * π)) := mul_le_mul_of_nonneg_left hI (by positivity)
          _ = M := by field_simp
      rw [hA_def, indicator_of_mem hx, norm_mul]
      calc ‖a x‖ * ‖circleKernel φ ε x‖ ≤ ‖a x‖ * M := mul_le_mul_of_nonneg_left hKM (norm_nonneg _)
        _ = M * ‖a x‖ := mul_comm _ _
    · have hz : ∀ θ : ℝ, φ (x - circleMap 0 ε θ) = 0 := by
        intro θ
        apply hφ0
        rw [mem_closedBall_zero_iff, not_le] at hx
        have h1 := norm_add_le (x - circleMap 0 ε θ) (circleMap 0 ε θ)
        rw [sub_add_cancel, norm_circleMap_zero_eq hε.le θ] at h1
        linarith
      have hK0 : circleKernel φ ε x = 0 := by
        unfold circleKernel
        simp only [hz, intervalIntegral.integral_zero, mul_zero]
      rw [hK0, mul_zero, norm_zero]
      exact mul_nonneg hM0 (hA0 x)
  have hKm : ∀ ε : ℝ, Measurable (circleKernel φ ε) := by
    intro ε
    have hc : Continuous fun p : ℂ × ℝ => φ (p.1 - circleMap 0 ε p.2) :=
      hφ.comp (continuous_fst.sub ((continuous_circleMap 0 ε).comp continuous_snd))
    have h := (hc.stronglyMeasurable).integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) (2 * π)))
    have h' : Measurable fun x : ℂ => ∫ y, φ (x - circleMap 0 ε y) ∂(volume.restrict (Ioc (0 : ℝ) (2 * π))) :=
      h.measurable
    have hfun : circleKernel φ ε = fun x => (2 * π)⁻¹ *
        ∫ y, φ (x - circleMap 0 ε y) ∂(volume.restrict (Ioc (0 : ℝ) (2 * π))) := by
      funext x
      unfold circleKernel
      rw [intervalIntegral.integral_of_le (by positivity)]
    rw [hfun]
    exact measurable_const.mul h'
  have hlim : Tendsto (fun ε => ∫ x, a x * circleKernel φ ε x) (𝓝[>] 0)
      (𝓝 (∫ x, a x * φ x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => M * A x) ?_ ?_
      (hAint.const_mul M) ?_
    · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
      exact (ha.mul (hKm ε)).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
      exact Eventually.of_forall fun x => hKb ε hε.1 hε.2.le x
    · exact Eventually.of_forall fun x => Tendsto.const_mul (a x) (tendsto_circleKernel hφ hφc x)
  have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∫ z, φ z * Real.circleAverage a z ε =
      ∫ x, a x * circleKernel φ ε x := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
    exact integral_mul_circleAverage_eq ha hloc hφ hφc hε.1 hε.2.le
  have hfinal : ∫ x, φ x * a x = ∫ x, a x * φ x := by
    congr 1
    funext x
    ring
  rw [hfinal]
  exact hlim.congr' (heq.mono fun ε h => h.symm)

end MatedCRT.LQGMeasure
