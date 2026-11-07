import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.KilledClockConvergence
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.OccupationDensity

/-! # Joint measurability of regularized occupation integrals -/

namespace MatedCRT

open MeasureTheory HarmonicBalls MarkovProcess Set Filter Topology
open scoped NNReal ENNReal

/-- A jointly measurable circle field gives a jointly measurable regularized
weighted occupation integral in the field and Brownian path variables. -/
theorem measurable_lqgClockApprox_weighted_occupation
    {Ω : Type*} [MeasurableSpace Ω] (γ ε : ℝ) (H : Ω → ℂ → ℝ)
    (hH : Measurable (fun p : Ω × ℂ => H p.1 p.2))
    (T : ℝ≥0) (f : ℂ → ℝ) (hf : Measurable f) :
    Measurable (fun p : Ω × ContinuousPath ℂ =>
      ∫ t in (0 : ℝ)..(T : ℝ), f (p.2 t.toNNReal) *
        (ε ^ (γ ^ 2 / 2) * Real.exp (γ * H p.1 (p.2 t.toNNReal)))) := by
  have heval : Measurable (fun q : (Ω × ContinuousPath ℂ) × ℝ =>
      q.1.2 q.2.toNNReal) := by
    exact (ContinuousEval.continuous_eval (F := ContinuousPath ℂ)).measurable.comp
      ((measurable_snd.comp measurable_fst).prodMk
        (continuous_real_toNNReal.measurable.comp measurable_snd))
  have hfield : Measurable (fun q : (Ω × ContinuousPath ℂ) × ℝ =>
      H q.1.1 (q.1.2 q.2.toNNReal)) :=
    hH.comp ((measurable_fst.comp measurable_fst).prodMk heval)
  have hint : Measurable (fun q : (Ω × ContinuousPath ℂ) × ℝ =>
      f (q.1.2 q.2.toNNReal) *
        (ε ^ (γ ^ 2 / 2) * Real.exp (γ * H q.1.1 (q.1.2 q.2.toNNReal)))) :=
    (hf.comp heval).mul (measurable_const.mul ((measurable_const.mul hfield).exp))
  have hm := hint.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) T))
  convert hm.measurable using 1
  funext p
  exact intervalIntegral.integral_of_le T.coe_nonneg

/-- The corresponding integrals of normalized occupation chaos are jointly
measurable in the field and path, when the field is spatially continuous. -/
theorem measurable_gmcApprox_occupation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ε : ℝ)
    (hε : 0 < ε) (H : Ω → ℂ → ℝ)
    (hH : Measurable (fun p : Ω × ℂ => H p.1 p.2))
    (hcont : ∀ ω, Continuous (H ω))
    (hvar : ∀ z, (∫ ω, (H ω z) ^ 2 ∂P) = Real.log ε⁻¹)
    (T : ℝ≥0) (f : ℂ → ℝ) (hf : Continuous f) :
    Measurable (fun p : Ω × ContinuousPath ℂ => ∫ z, f z ∂(gmcApprox P
      (pathOccupationMeasure (fun t => p.2 t.toNNReal) T) γ H p.1)) := by
  convert measurable_lqgClockApprox_weighted_occupation γ ε H hH T f hf.measurable using 1
  funext p
  rw [gmcApprox_eq_clock_density P _ γ ε hε H hvar p.1,
    pathOccupationMeasure_withDensity_integral p.2 T _ f (by fun_prop)
      (fun z => (mul_pos (Real.rpow_pos_of_pos hε _) (Real.exp_pos _)).le) hf]
  apply intervalIntegral.integral_congr
  intro t ht
  ring

/-- If a sequence of jointly measurable regularized clocks converges
pointwise to a continuous strictly increasing clock almost surely, the
resulting time-changed occupation integral is jointly measurable almost
everywhere. -/
theorem aestronglyMeasurable_clock_occupation_of_approx
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure (Ω × ContinuousPath ℂ))
    (γ : ℝ) (ε : ℕ → ℝ) (H : Ω → ℝ → ℂ → ℝ)
    (hεpos : ∀ n, 0 < ε n)
    (hH : ∀ n, Measurable (fun p : Ω × ℂ => H p.1 (ε n) p.2))
    (hcont : ∀ n ω, Continuous (H ω (ε n)))
    (G : (Ω × ContinuousPath ℂ) → ℝ≥0 → ℝ)
    (hG : ∀ᵐ p ∂Q, G p 0 = 0 ∧ Continuous (G p) ∧ StrictMono (G p) ∧
      ∀ t, Tendsto (fun n => lqgClockApprox γ (H p.1) (ε n) p.2 t)
        atTop (𝓝 (G p t)))
    (T : ℝ≥0) (f : ℂ → ℝ) (hf : Continuous f) (C : ℝ)
    (hbound : ∀ z, ‖f z‖ ≤ C) :
    AEStronglyMeasurable (fun p : Ω × ContinuousPath ℂ =>
      ∫ s in (0 : ℝ)..G p T, f (p.2 (clockInverse (G p) s.toNNReal))) Q := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n p => ∫ t in (0 : ℝ)..(T : ℝ), f (p.2 t.toNNReal) *
      (ε n ^ (γ ^ 2 / 2) * Real.exp (γ * H p.1 (ε n) (p.2 t.toNNReal))))
  · intro n
    exact (measurable_lqgClockApprox_weighted_occupation γ (ε n)
      (fun ω => H ω (ε n)) (hH n) T f hf.measurable).aestronglyMeasurable
  · filter_upwards [hG] with p hp
    exact tendsto_lqgClockApprox_weighted_occupation γ ε (H p.1) p.2 hεpos
      (fun n => hcont n p.1) (G p) hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 T f hf C hbound

end MatedCRT


