import MatedCRT.Proofs.Sec4.ConvergenceDivisible.BrownianExit
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ExitCDF

/-! Finite exit from an arbitrary ball for planar Brownian motion and LBM. -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory HarmonicBalls MarkovProcess Set Filter Metric
open scoped ENNReal NNReal Topology

/-- The real coordinate at a fixed time has mean equal to the starting real
coordinate and variance equal to the time. -/
theorem planarBrownianMotion_map_real_eval_from (y : ℂ) (t : ℝ≥0) :
    (planarBrownianMotion y).map (fun b => (b t).re) = gaussianReal y.re t := by
  have hreal := planarBrownianMotion_map_re y
  have heval : Measurable (fun b : ContinuousPath ℝ => b t) :=
    (ContinuousPath.continuous_eval t).measurable
  have hproj : Measurable (fun b : ContinuousPath ℂ => (reImPath b).1) :=
    measurable_fst.comp measurable_reImPath
  rw [← brownianMotion_map_eval t y.re, ← hreal, Measure.map_map heval hproj]
  rfl

/-- Planar Brownian motion leaves every ball in finite time, from any start. -/
theorem ae_planarBrownianMotion_exit_any_ball_lt_top (y z : ℂ) (r : ℝ) :
    ∀ᵐ b ∂planarBrownianMotion y, ContinuousPath.exitTime (ball z r) b < ⊤ := by
  let E : Set (ContinuousPath ℂ) := {b | ∀ t : ℝ≥0, b t ∈ ball z r}
  let K : ℝ := |z.re| + |r| + |y.re| + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hbound : ∀ n : ℕ, planarBrownianMotion y E ≤
      gaussianReal 0 1 {x : ℝ | |x| ≤ 1 / ((n : ℝ) + 1)} := by
    intro n
    let N : ℝ≥0 := (n : ℝ≥0) + 1
    let T : ℝ≥0 := (N * Real.toNNReal K) ^ 2
    have hN : (0 : ℝ) < N := by
      simp only [N, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
      positivity
    have hNK : 0 < (N : ℝ) * K := mul_pos hN hK
    have hsqrt : Real.sqrt (T : ℝ) = (N : ℝ) * K := by
      simp only [T, NNReal.coe_pow, NNReal.coe_mul, Real.coe_toNNReal _ hK.le,
        Real.sqrt_sq hNK.le]
    have hdist := planarBrownianMotion_map_real_eval_from y T
    have hsubset : E ⊆ (fun b : ContinuousPath ℂ => (b T).re) ⁻¹'
        {x : ℝ | |x - z.re| ≤ |r|} := by
      intro b hb
      have hbT : ‖b T - z‖ < r := by simpa [mem_ball, dist_eq_norm] using hb T
      have hreal := Complex.abs_re_le_norm (b T - z)
      change |(b T).re - z.re| ≤ |r|
      simp only [Complex.sub_re] at hreal
      linarith [le_abs_self r]
    calc
      planarBrownianMotion y E ≤ planarBrownianMotion y
          ((fun b : ContinuousPath ℂ => (b T).re) ⁻¹' {x : ℝ | |x - z.re| ≤ |r|}) :=
        measure_mono hsubset
      _ = gaussianReal y.re T {x : ℝ | |x - z.re| ≤ |r|} := by
        have hm : Measurable (fun b : ContinuousPath ℂ => (b T).re) :=
          (Complex.continuous_re.comp (ContinuousPath.continuous_eval T)).measurable
        rw [← hdist, Measure.map_apply hm (isClosed_le (by fun_prop) continuous_const).measurableSet]
      _ = gaussianReal 0 1 ((fun x : ℝ => y.re + ((N : ℝ) * K) * x) ⁻¹'
          {x : ℝ | |x - z.re| ≤ |r|}) := by
        rw [gaussianReal_eq_map_add_sqrt_mul, hsqrt]
        rw [Measure.map_apply (by fun_prop) (isClosed_le (by fun_prop) continuous_const).measurableSet]
      _ ≤ gaussianReal 0 1 {x : ℝ | |x| ≤ 1 / ((n : ℝ) + 1)} := by
        apply measure_mono
        intro x hx
        change |y.re + ((N : ℝ) * K) * x - z.re| ≤ |r| at hx
        have htriangle := abs_add_le (y.re + ((N : ℝ) * K) * x - z.re) (z.re - y.re)
        have heq : y.re + ((N : ℝ) * K) * x - z.re + (z.re - y.re) =
            ((N : ℝ) * K) * x := by ring
        rw [heq, abs_mul, abs_of_pos hNK] at htriangle
        have hzy := abs_sub z.re y.re
        have hscale : ((N : ℝ) * K) * |x| ≤ K := by
          dsimp [K] at *
          linarith
        have hle : (N : ℝ) * |x| ≤ 1 := by nlinarith
        change |x| ≤ 1 / ((n : ℝ) + 1)
        have hN' : (N : ℝ) = (n : ℝ) + 1 := by simp [N]
        rw [← hN']
        exact (le_div_iff₀ hN).2 (by simpa [mul_comm] using hle)
  have hzero : planarBrownianMotion y E = 0 := by
    apply le_antisymm _ bot_le
    exact le_of_tendsto_of_tendsto tendsto_const_nhds gaussianReal_shrinking_abs_tendsto_zero
      (Eventually.of_forall hbound)
  have hae : ∀ᵐ b ∂planarBrownianMotion y, b ∉ E := by
    apply ae_iff.mpr
    simpa using hzero
  filter_upwards [hae] with b hb
  apply (ContinuousPath.exitTime_lt_top_iff _ _).2
  simpa [E] using hb

/-- A strictly increasing LQG time change preserves finite exit from any ball. -/
theorem MatedCRTEnv.IsValid.ae_lbmExitTime_any_ball_lt_top
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} (hS : S.IsValid 𝒮 γ) (y z : ℂ) (r : ℝ) :
    ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y,
      lbmExitTime (S.clock ω) (ball z r) b < ⊤ := by
  filter_upwards [hS.isLQGClock] with ω hclock
  filter_upwards [(hclock y).2, ae_planarBrownianMotion_exit_any_ball_lt_top y z r] with b hb hfinite
  exact lbmExitTime_lt_top_of_exists_exit hb
    ((ContinuousPath.exitTime_lt_top_iff (ball z r) b).mp hfinite)

/-- Positive linear rescaling of LBM time preserves finite exit from any ball. -/
theorem MatedCRTEnv.IsValid.ae_rescaledLBMExitTime_any_ball_lt_top
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hm : 0 < S.m₀) (y z : ℂ) (r : ℝ) :
    ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y,
      pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b) < ⊤ := by
  filter_upwards [hS.isLQGClock] with ω hclock
  filter_upwards [(hclock y).2, ae_planarBrownianMotion_exit_any_ball_lt_top y z r] with b hb hfinite
  obtain ⟨s, hs⟩ := (ContinuousPath.exitTime_lt_top_iff (ball z r) b).mp hfinite
  let q : ℝ≥0 := Real.toNNReal (S.clock ω b s)
  let c : ℝ≥0 := Real.toNNReal S.m₀
  have hc : c ≠ 0 := by
    dsimp [c]
    exact ne_of_gt (Real.toNNReal_pos.mpr hm)
  have hexit : rescaledLBMPath (S.clock ω) S.m₀ b (q / c) ∉ ball z r := by
    change b (clockInverse (S.clock ω b) (c * (q / c))) ∉ ball z r
    rw [mul_div_cancel₀ q hc]
    dsimp [q]
    rw [clockInverse_clockValue hb.map_zero hb.strictMono s]
    exact hs
  have hbound : pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b) ≤
      ((q / c : ℝ≥0) : ℝ≥0∞) := by
    unfold pathExitTime
    exact sInf_le ⟨q / c, rfl, hexit⟩
  exact hbound.trans_lt ENNReal.coe_lt_top

/-- For an admissible parameter, the paper's normalized LBM exits every ball
in finite time for almost every environment and Brownian path. -/
theorem MatedCRTEnv.IsValid.ae_normalizedLBMExitTime_any_ball_lt_top
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ) (y z : ℂ) (r : ℝ) :
    ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y,
      pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b) < ⊤ := by
  have hc := matedCRTScalingConstantPositive 𝒮 γ hγ hγ2 Ω S hS
  have hdiv : 0 < (2 : ℝ) / S.m₀ := by
    simp only [MatedCRTEnv.c₀] at hc
    linarith
  have hm : 0 < S.m₀ := (div_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)).mp hdiv
  exact hS.ae_rescaledLBMExitTime_any_ball_lt_top hm y z r

end MatedCRT
