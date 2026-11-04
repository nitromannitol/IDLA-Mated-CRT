import MatedCRT.Proofs.Sec4.ConvergenceDivisible.BrownianExitTail
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.Median

/-! Annealed exit-time bounds from the clock and Brownian exit probabilities. -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory HarmonicBalls MarkovProcess Set Filter Metric
open scoped ENNReal NNReal Topology

/-- A bound on the early annealed exit distribution in terms of the clock and the
Brownian exit probability. -/
theorem MatedCRTEnv.IsValid.annealedExitCDF_le_clock_add_brownian
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} (hS : S.IsValid 𝒮 γ) (r q : ℝ≥0) :
    (∫⁻ ω, planarBrownianMotion 0
      {b | lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b ≤ (q : ℝ≥0∞)} ∂S.P) ≤
    (∫⁻ ω, planarBrownianMotion 0 {b | S.clock ω b r ≤ (q : ℝ)} ∂S.P) +
      planarBrownianMotion 0 {b | ∃ s ≤ r, b s ∉ ball 0 (1 / 2)} := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  let A := {b : ContinuousPath ℂ | ∃ s ≤ r, b s ∉ ball 0 (1 / 2)}
  let F : Ω → ℝ≥0∞ := fun ω => planarBrownianMotion 0 {b | S.clock ω b r ≤ (q : ℝ)}
  have hbound : ∀ᵐ ω ∂S.P, planarBrownianMotion 0
      {b | lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b ≤ (q : ℝ≥0∞)} ≤
        F ω + planarBrownianMotion 0 A := by
    filter_upwards [hS.isLQGClock] with ω hclock
    have hbad : planarBrownianMotion 0 {b | ¬ IsTimeChangeClock (S.clock ω b)} = 0 :=
      ae_iff.mp (hclock 0).2
    calc
      _ ≤ planarBrownianMotion 0
          ({b | ¬ IsTimeChangeClock (S.clock ω b)} ∪
           {b | Real.toNNReal (S.clock ω b r) ≤ q} ∪ A) :=
        measure_mono (lbmExitTime_event_subset r q)
      _ ≤ (planarBrownianMotion 0 {b | ¬ IsTimeChangeClock (S.clock ω b)} +
          planarBrownianMotion 0 {b | Real.toNNReal (S.clock ω b r) ≤ q}) +
          planarBrownianMotion 0 A := by
        exact (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ = F ω + planarBrownianMotion 0 A := by
        simp only [hbad, zero_add, F, Real.toNNReal_le_iff_le_coe]
  calc
    _ ≤ ∫⁻ ω, (F ω + planarBrownianMotion 0 A) ∂S.P := lintegral_mono_ae hbound
    _ = (∫⁻ ω, F ω ∂S.P) + planarBrownianMotion 0 A := by
      rw [lintegral_add_right _ measurable_const]
      simp

/-- The annealed exit distribution is below one half at a positive time. -/
theorem MatedCRTEnv.IsValid.exists_small_annealedExitCDF
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∃ δ : ℝ, 0 < δ ∧ (∫⁻ ω, planarBrownianMotion 0
      {b | lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b ≤ ENNReal.ofReal δ} ∂S.P) < 1 / 2 := by
  have hearly : ∀ᶠ n : ℕ in atTop, planarBrownianMotion 0
      {b | ∃ s : ℝ≥0, s ≤ ⟨1 / ((n : ℝ) + 1), by positivity⟩ ∧
        b s ∉ ball 0 (1 / 2)} < (1 / 8 : ℝ≥0∞) :=
    (tendsto_order.1 planarBrownianMotion_early_exit_tendsto_zero).2 (1 / 8 : ℝ≥0∞) (ENNReal.div_pos (by simp) (by simp))
  obtain ⟨n, hn⟩ := hearly.exists
  let r : ℝ≥0 := ⟨1 / ((n : ℝ) + 1), by positivity⟩
  have hr : 0 < r := by change 0 < 1 / ((n : ℝ) + 1); positivity
  have hclock : ∀ᶠ m : ℕ in atTop, (∫⁻ ω, planarBrownianMotion 0
      {b | S.clock ω b r ≤ 1 / ((m : ℝ) + 1)} ∂S.P) < (1 / 8 : ℝ≥0∞) :=
    (tendsto_order.1 (hS.annealed_clock_lower_tail_tendsto_zero hr)).2 (1 / 8 : ℝ≥0∞) (ENNReal.div_pos (by simp) (by simp))
  obtain ⟨m, hm⟩ := hclock.exists
  let q : ℝ≥0 := ⟨1 / ((m : ℝ) + 1), by positivity⟩
  have hq : (0 : ℝ) < q := by change 0 < 1 / ((m : ℝ) + 1); positivity
  refine ⟨q, hq, ?_⟩
  have hbound := hS.annealedExitCDF_le_clock_add_brownian r q
  have hsum : (∫⁻ ω, planarBrownianMotion 0 {b | S.clock ω b r ≤ (q : ℝ)} ∂S.P) +
      planarBrownianMotion 0 {b | ∃ s ≤ r, b s ∉ ball 0 (1 / 2)} < (1 / 2 : ℝ≥0∞) := by
    calc
      _ ≤ (1 / 8 : ℝ≥0∞) + 1 / 8 := add_le_add hm.le hn.le
      _ < 1 / 2 := by
        have hnum : ((1 / 8 + 1 / 8 : ℝ≥0) : ℝ≥0∞) < ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
          exact_mod_cast (show (1 / 8 : ℝ≥0) + 1 / 8 < 1 / 2 by norm_num)
        simpa using hnum
  simpa using hbound.trans_lt hsum

end MatedCRT
