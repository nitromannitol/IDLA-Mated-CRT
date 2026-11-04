import MatedCRT.Proofs.Sec4.ConvergenceDivisible.BrownianExit
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ClockTail
import MarkovProcess.Killed.Kernel

/-! Early and late exit estimates for planar Brownian motion. -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory HarmonicBalls MarkovProcess Set Filter Metric
open scoped ENNReal NNReal Topology

/-- The probability of exiting the ball before a shrinking deterministic time tends to zero. -/
theorem planarBrownianMotion_early_exit_tendsto_zero :
    Tendsto (fun n : ℕ => planarBrownianMotion 0
      {b | ∃ s : ℝ≥0, s ≤ ⟨1 / ((n : ℝ) + 1), by positivity⟩ ∧
        b s ∉ ball 0 (1 / 2)}) atTop (𝓝 0) := by
  let τ : ContinuousPath ℂ → ℝ≥0∞ := ContinuousPath.exitTime (ball 0 (1 / 2))
  have hm : AEMeasurable (fun b => (τ b).toReal) (planarBrownianMotion 0) :=
    (ENNReal.measurable_toReal.comp
      (ContinuousPath.measurable_exitTime _ isOpen_ball)).aemeasurable
  have hp : ∀ᵐ b ∂planarBrownianMotion 0, 0 < (τ b).toReal := by
    filter_upwards [ae_planarBrownianMotion_exit_ball_lt_top,
      ae_planarBrownianMotion_eval_zero 0] with b hfin hstart
    apply ENNReal.toReal_pos _ hfin.ne
    apply ne_of_gt
    apply (ContinuousPath.exitTime_pos_iff _ isOpen_ball b).2
    rw [hstart]
    simp
  have ht := measure_le_inv_nat_tendsto_zero hm hp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall fun _ => bot_le) ?_
  apply Eventually.of_forall
  intro n
  apply measure_mono_ae
  filter_upwards [ae_planarBrownianMotion_exit_ball_lt_top] with b hfin hb
  obtain ⟨s, hs, hout⟩ := hb
  let r : ℝ≥0 := ⟨1 / ((n : ℝ) + 1), by positivity⟩
  change s ≤ r at hs
  have he : τ b ≤ (r : ℝ≥0∞) := by
    exact (ContinuousPath.exitTime_le_of_notMem _ b s hout).trans (by exact_mod_cast hs)
  have := (ENNReal.toReal_le_toReal hfin.ne ENNReal.coe_ne_top).2 he
  change (τ b).toReal ≤ 1 / ((n : ℝ) + 1)
  rw [ENNReal.coe_toReal] at this
  exact this

/-- The probability of staying in the ball through an increasing deterministic time tends to zero. -/
theorem planarBrownianMotion_late_exit_tendsto_zero :
    Tendsto (fun n : ℕ => planarBrownianMotion 0
      {b | ∀ s : ℝ≥0, s ≤ (n : ℝ≥0) → b s ∈ ball 0 (1 / 2)}) atTop (𝓝 0) := by
  let τ : ContinuousPath ℂ → ℝ≥0∞ := ContinuousPath.exitTime (ball 0 (1 / 2))
  have hm : AEMeasurable (fun b => (τ b).toReal) (planarBrownianMotion 0) :=
    (ENNReal.measurable_toReal.comp
      (ContinuousPath.measurable_exitTime _ isOpen_ball)).aemeasurable
  have ht := measure_nat_le_tendsto_zero hm
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall fun _ => bot_le) ?_
  apply Eventually.of_forall
  intro n
  apply measure_mono_ae
  filter_upwards [ae_planarBrownianMotion_exit_ball_lt_top] with b hfin hb
  have he : ((n : ℝ≥0) : ℝ≥0∞) ≤ τ b := by
    by_contra hn
    have hhit := (ContinuousPath.exitTime_le_iff_mem_hitsSetBy _ isOpen_ball (n : ℝ≥0) b).1
      (le_of_lt (lt_of_not_ge hn))
    obtain ⟨s, hs⟩ := hhit
    exact hs (hb s s.property)
  have := (ENNReal.toReal_le_toReal ENNReal.coe_ne_top hfin.ne).2 he
  simpa [τ] using this

end MatedCRT

