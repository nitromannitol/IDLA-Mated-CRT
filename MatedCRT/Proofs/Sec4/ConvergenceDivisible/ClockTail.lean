import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ClockMeasurable

/-! Quenched tail bounds for deterministic-time Liouville clock values. -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory HarmonicBalls MarkovProcess Set Filter Metric
open scoped ENNReal NNReal Topology

/-- A positive almost everywhere measurable random variable has vanishing lower
tail at zero under any finite measure. -/
theorem measure_le_inv_nat_tendsto_zero {α : Type} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ} (hf : AEMeasurable f μ)
    (hpos : ∀ᵐ x ∂μ, 0 < f x) :
    Tendsto (fun n : ℕ => μ {x | f x ≤ 1 / ((n : ℝ) + 1)}) atTop (𝓝 0) := by
  let A : ℕ → Set α := fun n => {x | f x ≤ 1 / ((n : ℝ) + 1)}
  have hmeas : ∀ n, NullMeasurableSet (A n) μ := fun _ =>
    nullMeasurableSet_le hf aemeasurable_const
  have hanti : Antitone A := by
    intro n m hnm x hx
    change f x ≤ 1 / ((m : ℝ) + 1) at hx
    change f x ≤ 1 / ((n : ℝ) + 1)
    have hnm' : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
    exact le_trans hx (one_div_le_one_div_of_le (by positivity) hnm')
  have hinter : (⋂ n, A n) ⊆ {x | ¬ 0 < f x} := by
    intro x hx
    have hall : ∀ n : ℕ, f x ≤ 1 / ((n : ℝ) + 1) := fun n => mem_iInter.mp hx n
    have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hx0 : f x ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (Eventually.of_forall hall)
    exact not_lt_of_ge hx0
  have hzero : μ (⋂ n, A n) = 0 := measure_mono_null hinter (ae_iff.mp hpos)
  have hlim := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top _ _⟩
  rw [hzero] at hlim
  exact hlim

/-- The upper tail of a real random variable vanishes at infinity under a finite
measure, provided it is measurable modulo null sets. -/
theorem measure_nat_le_tendsto_zero {α : Type} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ} (hf : AEMeasurable f μ) :
    Tendsto (fun n : ℕ => μ {x | (n : ℝ) ≤ f x}) atTop (𝓝 0) := by
  let A : ℕ → Set α := fun n => {x | (n : ℝ) ≤ f x}
  have hmeas : ∀ n, NullMeasurableSet (A n) μ := fun _ =>
    nullMeasurableSet_le aemeasurable_const hf
  have hanti : Antitone A := by
    intro n m hnm x hx
    change (m : ℝ) ≤ f x at hx
    change (n : ℝ) ≤ f x
    exact le_trans (Nat.cast_le.mpr hnm) hx
  have hempty : (⋂ n, A n) = ∅ := by
    apply eq_empty_of_forall_notMem
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_gt (f x)
    exact (not_le_of_gt hn) (mem_iInter.mp hx n)
  have hlim := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top _ _⟩
  rw [hempty, measure_empty] at hlim
  exact hlim

/-- For almost every valid environment, the clock at each positive deterministic
time has vanishing lower and upper tails under the Brownian law. -/
theorem MatedCRTEnv.IsValid.ae_clock_tail_limits
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ r : ℝ≥0, 0 < r →
      Tendsto (fun n : ℕ => planarBrownianMotion 0
        {b | S.clock ω b r ≤ 1 / ((n : ℝ) + 1)}) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => planarBrownianMotion 0
        {b | (n : ℝ) ≤ S.clock ω b r}) atTop (𝓝 0) := by
  filter_upwards [hS.isLQGClock, hS.ae_clock_aemeasurable_at_time] with ω hclock hmeas
  intro r hr
  have hpos : ∀ᵐ b ∂planarBrownianMotion 0, 0 < S.clock ω b r := by
    filter_upwards [(hclock 0).2] with b hb
    simpa [hb.map_zero] using hb.strictMono hr
  exact ⟨measure_le_inv_nat_tendsto_zero (hmeas r) hpos, measure_nat_le_tendsto_zero (hmeas r)⟩

end MatedCRT
