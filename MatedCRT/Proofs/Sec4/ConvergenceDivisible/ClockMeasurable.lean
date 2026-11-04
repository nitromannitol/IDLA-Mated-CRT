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

/-- At each positive radius the circle-average field has a jointly measurable
version which agrees simultaneously at every spatial point almost surely. -/
theorem IsQuantumCone.exists_measurable_circle_version
    {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hcone : IsQuantumCone γ P hC hcirc) {r : ℝ} (hr : 0 < r) :
    ∃ H : Ω → ℂ → ℝ, Measurable (fun p : Ω × ℂ => H p.1 p.2) ∧
      ∀ᵐ ω ∂P, ∀ z, H ω z = hcirc ω r z := by
  classical
  have hcont : ∀ᵐ ω ∂P, Continuous (hcirc ω r) := by
    filter_upwards [hcone.ae_continuousOn_circle] with ω hω
    apply continuousOn_univ.mp
    apply hω.comp (continuous_const.prodMk continuous_id).continuousOn
    intro z _
    exact ⟨hr, mem_univ z⟩
  obtain ⟨bad, hsub, hbad, hzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hcont)
  let H : Ω → ℂ → ℝ := fun ω z => if ω ∈ bad then 0 else hcirc ω r z
  have hHcont : ∀ ω, Continuous (H ω) := by
    intro ω
    by_cases hω : ω ∈ bad
    · simpa [H, hω] using (continuous_const : Continuous (fun _ : ℂ => (0 : ℝ)))
    · have hh : Continuous (hcirc ω r) := by
        by_contra hn
        exact hω (hsub hn)
      simpa [H, hω] using hh
  have hHmeas : ∀ z, Measurable (fun ω => H ω z) := by
    intro z
    change Measurable (fun ω => if ω ∈ bad then (0 : ℝ) else hcirc ω r z)
    exact measurable_const.ite hbad (hcone.measurable_circle r z hr)
  have hjoint : Measurable (fun p : ℂ × Ω => H p.2 p.1) :=
    measurable_uncurry_of_continuous_of_measurable hHcont hHmeas
  refine ⟨H, hjoint.comp measurable_swap, ?_⟩
  have hae : ∀ᵐ ω ∂P, ω ∉ bad := by
    apply ae_iff.mpr
    simpa using hzero
  filter_upwards [hae] with ω hω z
  simp [H, hω]

/-- Integrating a jointly measurable circle-average version along Brownian paths
gives a jointly measurable regularized clock. -/
theorem measurable_lqgClockApprox_joint {Ω : Type} [MeasurableSpace Ω]
    {H : Ω → ℂ → ℝ} (hH : Measurable (fun p : Ω × ℂ => H p.1 p.2))
    (γ ε : ℝ) (t : ℝ≥0) :
    Measurable (fun p : Ω × ContinuousPath ℂ =>
      ∫ s in (0 : ℝ)..(t : ℝ), ε ^ (γ ^ 2 / 2) * Real.exp (γ * H p.1 (p.2 s.toNNReal))) := by
  have heval : Measurable (fun p : (Ω × ContinuousPath ℂ) × ℝ => p.1.2 p.2.toNNReal) := by
    have hc : Continuous (fun p : ContinuousPath ℂ × ℝ => p.1 p.2.toNNReal) :=
      ContinuousEval.continuous_eval.comp
        (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))
    exact hc.measurable.comp (measurable_fst.snd.prodMk measurable_snd)
  have hfield : Measurable (fun p : (Ω × ContinuousPath ℂ) × ℝ =>
      H p.1.1 (p.1.2 p.2.toNNReal)) := hH.comp (measurable_fst.fst.prodMk heval)
  have hint : Measurable (fun p : (Ω × ContinuousPath ℂ) × ℝ =>
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * H p.1.1 (p.1.2 p.2.toNNReal))) :=
    measurable_const.mul (Real.continuous_exp.measurable.comp (measurable_const.mul hfield))
  have hm := hint.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc 0 (t : ℝ)))
  simpa [intervalIntegral.integral_of_le t.coe_nonneg] using hm.measurable

/-- Each dyadic clock approximation has a jointly measurable version agreeing
with it for every path outside one null set of environments. -/
theorem IsQuantumCone.exists_measurable_clockApprox_version
    {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hcone : IsQuantumCone γ P hC hcirc) (k : ℕ) (t : ℝ≥0) :
    ∃ G : Ω × ContinuousPath ℂ → ℝ, Measurable G ∧
      ∀ᵐ ω ∂P, ∀ b, G (ω, b) = lqgClockApprox γ (hcirc ω) (dyadicScale k) b t := by
  obtain ⟨H, hH, hsame⟩ := IsQuantumCone.exists_measurable_circle_version hcone (dyadicScale_pos k)
  refine ⟨fun p => ∫ s in (0 : ℝ)..(t : ℝ),
    (dyadicScale k) ^ (γ ^ 2 / 2) * Real.exp (γ * H p.1 (p.2 s.toNNReal)),
    measurable_lqgClockApprox_joint hH γ (dyadicScale k) t, ?_⟩
  filter_upwards [hsame] with ω hω b
  unfold lqgClockApprox
  congr 1
  funext s
  rw [hω]

end MatedCRT
