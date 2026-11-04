import MatedCRT.Proofs.Sec4.ConvergenceDivisible.BrownianExit

/-! Measurability of the Liouville clock at deterministic times. -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory HarmonicBalls MarkovProcess Set Filter Metric
open scoped ENNReal NNReal Topology

/-- A regularized clock is measurable in the Brownian path when the corresponding
circle average is continuous. -/
theorem measurable_lqgClockApprox {γ ε : ℝ} {hε : ℝ → ℂ → ℝ}
    (hcont : Continuous (hε ε)) (t : ℝ≥0) :
    Measurable (fun b : ContinuousPath ℂ => lqgClockApprox γ hε ε b t) := by
  have heval : Continuous (fun p : ContinuousPath ℂ × ℝ => p.1 p.2.toNNReal) := by
    exact ContinuousEval.continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))
  have hint : Continuous (fun p : ContinuousPath ℂ × ℝ =>
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (p.1 p.2.toNNReal))) := by
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (hcont.comp heval)))
  have hm := hint.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc 0 (t : ℝ)))
  simpa [lqgClockApprox, intervalIntegral.integral_of_le t.coe_nonneg] using hm.measurable

/-- Uniform convergence in probability of regularized clocks implies convergence
in probability at each deterministic Brownian time. -/
theorem IsLQGClock.tendstoInMeasure_at_time {Q : ProbabilityTheory.Kernel ℂ (ContinuousPath ℂ)}
    {γ : ℝ} {hε : ℝ → ℂ → ℝ} {x : ℂ} {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : IsLQGClock Q γ hε x F) (t : ℝ≥0) :
    TendstoInMeasure (Q x) (fun k b => lqgClockApprox γ hε (dyadicScale k) b t)
      atTop (fun b => F b t) := by
  apply tendstoInMeasure_iff_dist.mpr
  intro δ hδ
  have hlim := hF t δ hδ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  apply Eventually.of_forall
  intro k
  apply measure_mono
  intro b hb
  exact ⟨t, le_rfl, by simpa [Real.dist_eq] using hb⟩

/-- A clock given by the regularization limit is almost everywhere measurable at
each deterministic time. -/
theorem IsLQGClock.aemeasurable_at_time {Q : ProbabilityTheory.Kernel ℂ (ContinuousPath ℂ)}
    {γ : ℝ} {hε : ℝ → ℂ → ℝ} {x : ℂ} {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : IsLQGClock Q γ hε x F) (hcont : ∀ k, Continuous (hε (dyadicScale k)))
    (t : ℝ≥0) : AEMeasurable (fun b => F b t) (Q x) :=
  (IsLQGClock.tendstoInMeasure_at_time hF t).aemeasurable
    (fun k => (measurable_lqgClockApprox (hcont k) t).aemeasurable)

/-- In a valid environment, every deterministic-time clock value is measurable
modulo the Brownian path law. The exceptional set of environments is independent
of the time. -/
theorem MatedCRTEnv.IsValid.ae_clock_aemeasurable_at_time
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ t : ℝ≥0, AEMeasurable (fun b => S.clock ω b t) (planarBrownianMotion 0) := by
  filter_upwards [hS.isLQGClock, hS.isQuantumCone.ae_continuousOn_circle] with ω hclock hcircle
  have hcont : ∀ k, Continuous (S.hcirc ω (dyadicScale k)) := by
    intro k
    apply continuousOn_univ.mp
    apply hcircle.comp (continuous_const.prodMk continuous_id).continuousOn
    intro z _
    exact ⟨dyadicScale_pos k, mem_univ z⟩
  intro t
  exact IsLQGClock.aemeasurable_at_time (hclock 0).1 hcont t

end MatedCRT
