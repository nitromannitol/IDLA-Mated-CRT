import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ClockMeasurable
import MatedCRT.LPStaging.Prob.MeasureLiminfTails

/-! Quenched tail bounds for deterministic-time Liouville clock values. -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory HarmonicBalls MarkovProcess Set Filter Metric
open scoped ENNReal NNReal Topology

/-- Convergence in measure sandwiches the limiting probability of a lower-tail
event between probabilities at slightly smaller and larger thresholds. -/
theorem lowerTail_liminf_bounds_of_tendstoInMeasure {α : Type} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} {g : α → ℝ}
    (hfg : TendstoInMeasure μ f atTop g) {a δ : ℝ} (hδ : 0 < δ) :
    μ {x | g x ≤ a} ≤ liminf (fun k => μ {x | f k x ≤ a + δ}) atTop ∧
      liminf (fun k => μ {x | f k x ≤ a + δ}) atTop ≤ μ {x | g x ≤ a + 2 * δ} :=
  LatticeProb.MeasureLiminfTails.lowerTail_liminf_bounds_of_tendstoInMeasure hfg hδ

/-- The analogous probability sandwich for upper-tail events. -/
theorem upperTail_liminf_bounds_of_tendstoInMeasure {α : Type} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} {g : α → ℝ}
    (hfg : TendstoInMeasure μ f atTop g) {a δ : ℝ} (hδ : 0 < δ) :
    μ {x | a ≤ g x} ≤ liminf (fun k => μ {x | a - δ ≤ f k x}) atTop ∧
      liminf (fun k => μ {x | a - δ ≤ f k x}) atTop ≤ μ {x | a - 2 * δ ≤ g x} :=
  LatticeProb.MeasureLiminfTails.upperTail_liminf_bounds_of_tendstoInMeasure hfg hδ

/-- Lower-tail probabilities of a jointly measurable function are measurable in
the environment variable. -/
theorem measurable_measure_joint_lowerTail {Ω β : Type} [MeasurableSpace Ω] [MeasurableSpace β]
    {ν : Measure β} [SFinite ν] {F : Ω × β → ℝ} (hF : Measurable F) (a : ℝ) :
    Measurable (fun ω => ν {b | F (ω, b) ≤ a}) :=
  LatticeProb.MeasureLiminfTails.measurable_measure_joint_lowerTail hF a

/-- Upper-tail probabilities of a jointly measurable function are measurable in
the environment variable. -/
theorem measurable_measure_joint_upperTail {Ω β : Type} [MeasurableSpace Ω] [MeasurableSpace β]
    {ν : Measure β} [SFinite ν] {F : Ω × β → ℝ} (hF : Measurable F) (a : ℝ) :
    Measurable (fun ω => ν {b | a ≤ F (ω, b)}) :=
  LatticeProb.MeasureLiminfTails.measurable_measure_joint_upperTail hF a

/-- The quenched lower clock tail admits measurable probability envelopes with
arbitrarily close thresholds. -/
theorem MatedCRTEnv.IsValid.exists_measurable_lower_clock_tail_envelopes
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} (hS : S.IsValid 𝒮 γ) (r : ℝ≥0) :
    ∃ E : ℕ → Ω → ℝ≥0∞, (∀ n, Measurable (E n)) ∧
      ∀ᵐ ω ∂S.P, ∀ n : ℕ,
        planarBrownianMotion 0 {b | S.clock ω b r ≤ 1 / ((n : ℝ) + 1)} ≤ E n ω ∧
        E n ω ≤ planarBrownianMotion 0 {b | S.clock ω b r ≤ 3 / ((n : ℝ) + 1)} := by
  classical
  choose G hGmeas hGsame using fun k : ℕ =>
    IsQuantumCone.exists_measurable_clockApprox_version hS.isQuantumCone k r
  let E : ℕ → Ω → ℝ≥0∞ := fun n ω => liminf (fun k => planarBrownianMotion 0
    {b | G k (ω, b) ≤ 2 / ((n : ℝ) + 1)}) atTop
  refine ⟨E, ?_, ?_⟩
  · intro n
    exact Measurable.liminf (fun k => measurable_measure_joint_lowerTail (hGmeas k) _)
  · filter_upwards [hS.isLQGClock, ae_all_iff.mpr hGsame] with ω hclock hsame
    intro n
    have hconv : TendstoInMeasure (planarBrownianMotion 0) (fun k b => G k (ω, b)) atTop
        (fun b => S.clock ω b r) := by
      have h := IsLQGClock.tendstoInMeasure_at_time (hclock 0).1 r
      have heq : (fun k b => G k (ω, b)) =
          (fun k b => lqgClockApprox γ (S.hcirc ω) (dyadicScale k) b r) := by
        funext k b
        exact hsame k b
      rw [heq]
      exact h
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have h := lowerTail_liminf_bounds_of_tendstoInMeasure hconv (a := 1 / ((n : ℝ) + 1)) hpos
    convert h using 1 <;> simp only [E] <;> try ring

/-- A positive almost everywhere measurable random variable has vanishing lower
tail at zero under any finite measure. -/
theorem measure_le_inv_nat_tendsto_zero {α : Type} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ} (hf : AEMeasurable f μ)
    (hpos : ∀ᵐ x ∂μ, 0 < f x) :
    Tendsto (fun n : ℕ => μ {x | f x ≤ 1 / ((n : ℝ) + 1)}) atTop (𝓝 0) :=
  LatticeProb.MeasureLiminfTails.measure_le_inv_nat_tendsto_zero hf hpos

/-- The upper tail of a real random variable vanishes at infinity under a finite
measure, provided it is measurable modulo null sets. -/
theorem measure_nat_le_tendsto_zero {α : Type} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ} (hf : AEMeasurable f μ) :
    Tendsto (fun n : ℕ => μ {x | (n : ℝ) ≤ f x}) atTop (𝓝 0) :=
  LatticeProb.MeasureLiminfTails.measure_nat_le_tendsto_zero hf

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

/-- The annealed probability that the clock at a positive deterministic time is
very small tends to zero. -/
theorem MatedCRTEnv.IsValid.annealed_clock_lower_tail_tendsto_zero
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} (hS : S.IsValid 𝒮 γ) {r : ℝ≥0} (hr : 0 < r) :
    Tendsto (fun n : ℕ => ∫⁻ ω, planarBrownianMotion 0
      {b | S.clock ω b r ≤ 1 / ((n : ℝ) + 1)} ∂S.P) atTop (𝓝 0) := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨E, hEmeas, hEsand⟩ := hS.exists_measurable_lower_clock_tail_envelopes r
  have hElim : ∀ᵐ ω ∂S.P, Tendsto (fun n => E n ω) atTop (𝓝 0) := by
    filter_upwards [hEsand, hS.isLQGClock, hS.ae_clock_aemeasurable_at_time] with ω hE hc hm
    have hpos : ∀ᵐ b ∂planarBrownianMotion 0, 0 < S.clock ω b r / 3 := by
      filter_upwards [(hc 0).2] with b hb
      have hh : 0 < S.clock ω b r := by simpa [hb.map_zero] using hb.strictMono hr
      positivity
    have ht := measure_le_inv_nat_tendsto_zero ((hm r).div_const 3) hpos
    have ht' : Tendsto (fun n : ℕ => planarBrownianMotion 0
        {b | S.clock ω b r ≤ 3 / ((n : ℝ) + 1)}) atTop (𝓝 0) := by
      convert ht using 1
      funext n
      congr 1
      ext b
      simp only [mem_ofPred_eq, div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
      have heq : (3 : ℝ) / ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) * 3 := by ring
      rw [heq]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht'
      (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun n => (hE n).2)
  have hEbound : ∀ n, E n ≤ᵐ[S.P] fun _ => (1 : ℝ≥0∞) := by
    intro n
    filter_upwards [hEsand] with ω hE
    calc
      E n ω ≤ planarBrownianMotion 0 {b | S.clock ω b r ≤ 3 / ((n : ℝ) + 1)} := (hE n).2
      _ ≤ planarBrownianMotion 0 univ := measure_mono (subset_univ _)
      _ = 1 := measure_univ
  have hEint := tendsto_lintegral_of_dominated_convergence (fun _ => 1) hEmeas hEbound
    (by simp) hElim
  have hEint' : Tendsto (fun n => ∫⁻ ω, E n ω ∂S.P) atTop (𝓝 0) := by
    simpa using hEint
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hEint'
    (Eventually.of_forall fun _ => bot_le) ?_
  apply Eventually.of_forall
  intro n
  apply lintegral_mono_ae
  filter_upwards [hEsand] with ω hE
  exact (hE n).1

/-- Measurable envelopes for the upper tail of the clock. -/
theorem MatedCRTEnv.IsValid.exists_measurable_upper_clock_tail_envelopes
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} (hS : S.IsValid 𝒮 γ) (r : ℝ≥0) :
    ∃ E : ℕ → Ω → ℝ≥0∞, (∀ n, Measurable (E n)) ∧
      ∀ᵐ ω ∂S.P, ∀ n : ℕ,
        planarBrownianMotion 0 {b | 3 * ((n : ℝ) + 1) ≤ S.clock ω b r} ≤ E n ω ∧
        E n ω ≤ planarBrownianMotion 0 {b | (n : ℝ) + 1 ≤ S.clock ω b r} := by
  classical
  choose G hGmeas hGsame using fun k : ℕ =>
    IsQuantumCone.exists_measurable_clockApprox_version hS.isQuantumCone k r
  let E : ℕ → Ω → ℝ≥0∞ := fun n ω => liminf (fun k => planarBrownianMotion 0
    {b | 2 * ((n : ℝ) + 1) ≤ G k (ω, b)}) atTop
  refine ⟨E, ?_, ?_⟩
  · intro n
    exact Measurable.liminf (fun k => measurable_measure_joint_upperTail (hGmeas k) _)
  · filter_upwards [hS.isLQGClock, ae_all_iff.mpr hGsame] with ω hclock hsame
    intro n
    have hconv : TendstoInMeasure (planarBrownianMotion 0) (fun k b => G k (ω, b)) atTop
        (fun b => S.clock ω b r) := by
      have h := IsLQGClock.tendstoInMeasure_at_time (hclock 0).1 r
      have heq : (fun k b => G k (ω, b)) =
          (fun k b => lqgClockApprox γ (S.hcirc ω) (dyadicScale k) b r) := by
        funext k b
        exact hsame k b
      rw [heq]
      exact h
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h := upperTail_liminf_bounds_of_tendstoInMeasure hconv
      (a := 3 * ((n : ℝ) + 1)) hpos
    convert h using 1 <;> simp only [E] <;> try ring

/-- The annealed upper tail of the clock at positive deterministic time tends to zero. -/
theorem MatedCRTEnv.IsValid.annealed_clock_upper_tail_tendsto_zero
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} (hS : S.IsValid 𝒮 γ) {r : ℝ≥0} (hr : 0 < r) :
    Tendsto (fun n : ℕ => ∫⁻ ω, planarBrownianMotion 0
      {b | 3 * ((n : ℝ) + 1) ≤ S.clock ω b r} ∂S.P) atTop (𝓝 0) := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨E, hEmeas, hEsand⟩ := hS.exists_measurable_upper_clock_tail_envelopes r
  have hElim : ∀ᵐ ω ∂S.P, Tendsto (fun n => E n ω) atTop (𝓝 0) := by
    filter_upwards [hEsand, hS.ae_clock_tail_limits] with ω hE ht
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (ht r hr).2
      (Eventually.of_forall fun _ => bot_le) ?_
    apply Eventually.of_forall
    intro n
    calc
      E n ω ≤ planarBrownianMotion 0 {b | (n : ℝ) + 1 ≤ S.clock ω b r} := (hE n).2
      _ ≤ planarBrownianMotion 0 {b | (n : ℝ) ≤ S.clock ω b r} := by
        apply measure_mono
        intro b hb
        change (n : ℝ) + 1 ≤ S.clock ω b r at hb
        change (n : ℝ) ≤ S.clock ω b r
        linarith
  have hEbound : ∀ n, E n ≤ᵐ[S.P] fun _ => (1 : ℝ≥0∞) := by
    intro n
    filter_upwards [hEsand] with ω hE
    calc
      E n ω ≤ planarBrownianMotion 0 {b | (n : ℝ) + 1 ≤ S.clock ω b r} := (hE n).2
      _ ≤ planarBrownianMotion 0 univ := measure_mono (subset_univ _)
      _ = 1 := measure_univ
  have hEint := tendsto_lintegral_of_dominated_convergence (fun _ => 1) hEmeas hEbound
    (by simp) hElim
  have hEint' : Tendsto (fun n => ∫⁻ ω, E n ω ∂S.P) atTop (𝓝 0) := by
    simpa using hEint
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hEint'
    (Eventually.of_forall fun _ => bot_le) ?_
  apply Eventually.of_forall
  intro n
  apply lintegral_mono_ae
  filter_upwards [hEsand] with ω hE
  exact (hE n).1

end MatedCRT
