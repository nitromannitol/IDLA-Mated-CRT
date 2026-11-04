import MatedCRT.Proofs.Sec4.ConvergenceDivisible.TimeChange

/-! Planar Brownian motion exits a bounded ball almost surely. -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory HarmonicBalls MarkovProcess Set Filter Metric
open scoped ENNReal NNReal Topology

/-- A standard Gaussian assigns vanishing mass to intervals shrinking to zero. -/
theorem gaussianReal_shrinking_abs_tendsto_zero :
    Tendsto (fun n : ℕ => gaussianReal 0 1 {x : ℝ | |x| ≤ 1 / ((n : ℝ) + 1)})
      atTop (𝓝 0) := by
  let A : ℕ → Set ℝ := fun n => {x | |x| ≤ 1 / ((n : ℝ) + 1)}
  have hmeas : ∀ n, NullMeasurableSet (A n) (gaussianReal 0 1) := by
    intro n
    exact (isClosed_le continuous_abs continuous_const).measurableSet.nullMeasurableSet
  have hanti : Antitone A := by
    intro n m hnm x hx
    change |x| ≤ 1 / ((m : ℝ) + 1) at hx
    change |x| ≤ 1 / ((n : ℝ) + 1)
    have hnm' : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
    exact le_trans hx (one_div_le_one_div_of_le (by positivity) hnm')
  have hinter : (⋂ n, A n) ⊆ ({0} : Set ℝ) := by
    intro x hx
    have hall : ∀ n : ℕ, |x| ≤ 1 / ((n : ℝ) + 1) := fun n => mem_iInter.mp hx n
    have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hx0 : |x| ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (Eventually.of_forall hall)
    simpa using abs_eq_zero.mp (le_antisymm hx0 (abs_nonneg _))
  have hzero : gaussianReal 0 1 (⋂ n, A n) = 0 := by
    let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
    exact measure_mono_null hinter (measure_singleton 0)
  have hlim := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top _ _⟩
  rw [hzero] at hlim
  exact hlim

/-- Every fixed-time real coordinate of planar Brownian motion has the expected
one-dimensional Gaussian law. -/
theorem planarBrownianMotion_map_real_eval (t : ℝ≥0) :
    (planarBrownianMotion 0).map (fun b => (b t).re) = gaussianReal 0 t := by
  have hreal := planarBrownianMotion_map_re 0
  simp only [Complex.zero_re] at hreal
  have heval : Measurable (fun b : ContinuousPath ℝ => b t) :=
    (ContinuousPath.continuous_eval t).measurable
  have hproj : Measurable (fun b : ContinuousPath ℂ => (reImPath b).1) :=
    measurable_fst.comp measurable_reImPath
  rw [← brownianMotion_map_eval t 0, ← hreal, Measure.map_map heval hproj]
  rfl

/-- Planar Brownian motion started at zero exits the ball of radius one half
in finite time almost surely. -/
theorem ae_planarBrownianMotion_exit_ball_lt_top :
    ∀ᵐ b ∂planarBrownianMotion 0,
      ContinuousPath.exitTime (ball 0 (1 / 2)) b < ⊤ := by
  let E : Set (ContinuousPath ℂ) := {b | ∀ t : ℝ≥0, b t ∈ ball 0 (1 / 2)}
  have hbound : ∀ n : ℕ, planarBrownianMotion 0 E ≤
      gaussianReal 0 1 {x : ℝ | |x| ≤ 1 / ((n : ℝ) + 1)} := by
    intro n
    let N : ℝ≥0 := (n : ℝ≥0) + 1
    let T : ℝ≥0 := N ^ 2
    have hN : (0 : ℝ) < N := by
      simp only [N, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
      positivity
    have hsqrt : Real.sqrt (T : ℝ) = (N : ℝ) := by
      simp [T, Real.sqrt_sq (le_of_lt hN)]
    have hdist := planarBrownianMotion_map_real_eval T
    have hsubset : E ⊆ (fun b : ContinuousPath ℂ => (b T).re) ⁻¹'
        {x : ℝ | |x| ≤ 1} := by
      intro b hb
      have hbT : ‖b T‖ < (1 / 2 : ℝ) := by simpa [mem_ball, dist_zero_right] using hb T
      have hreal := Complex.abs_re_le_norm (b T)
      change |(b T).re| ≤ 1
      linarith
    calc
      planarBrownianMotion 0 E ≤ planarBrownianMotion 0
          ((fun b : ContinuousPath ℂ => (b T).re) ⁻¹' {x : ℝ | |x| ≤ 1}) := measure_mono hsubset
      _ = gaussianReal 0 T {x : ℝ | |x| ≤ 1} := by
        have hmeas : Measurable (fun b : ContinuousPath ℂ => (b T).re) :=
          (Complex.continuous_re.comp (ContinuousPath.continuous_eval T)).measurable
        rw [← hdist, Measure.map_apply hmeas
          (isClosed_le continuous_abs continuous_const).measurableSet]
      _ = gaussianReal 0 1 ((fun x : ℝ => (N : ℝ) * x) ⁻¹' {x : ℝ | |x| ≤ 1}) := by
        rw [gaussianReal_eq_map_add_sqrt_mul, hsqrt]
        simp only [zero_add]
        rw [Measure.map_apply (by fun_prop) (isClosed_le continuous_abs continuous_const).measurableSet]
      _ ≤ gaussianReal 0 1 {x : ℝ | |x| ≤ 1 / ((n : ℝ) + 1)} := by
        apply measure_mono
        intro x hx
        change |(N : ℝ) * x| ≤ 1 at hx
        rw [abs_mul, abs_of_nonneg hN.le] at hx
        change |x| ≤ 1 / ((n : ℝ) + 1)
        have hN' : (N : ℝ) = (n : ℝ) + 1 := by simp [N]
        rw [← hN']
        exact (le_div_iff₀ hN).2 (by simpa [mul_comm] using hx)
  have hzero : planarBrownianMotion 0 E = 0 := by
    apply le_antisymm _ bot_le
    exact le_of_tendsto_of_tendsto tendsto_const_nhds gaussianReal_shrinking_abs_tendsto_zero
      (Eventually.of_forall hbound)
  have hae : ∀ᵐ b ∂planarBrownianMotion 0, b ∉ E := by
    apply ae_iff.mpr
    simpa using hzero
  filter_upwards [hae] with b hb
  apply (ContinuousPath.exitTime_lt_top_iff _ _).2
  simpa [E] using hb

/-- Liouville Brownian motion exits the radius-one-half ball in finite time for
almost every valid environment and almost every Brownian path. -/
theorem MatedCRTEnv.IsValid.ae_lbmExitTime_lt_top
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion 0,
      lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b < ⊤ :=
  hS.ae_lbmExitTime_lt_top_of_ae_brownianExitTime_lt_top
    ae_planarBrownianMotion_exit_ball_lt_top

end MatedCRT
