import MatedCRT.FirstPass.Derived.ConeReferenceStoppedHeatBound
import MatedCRT.FirstPass.Derived.PlanarBrownianExitDynkin
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ClockMeasurable
import LatticeProb.Prob.MeasureLiminfTails

/-!
# The approximating LQG clocks of the reference cone are small at small times

Let `h_ε` be the circle averages of a field and `A_k(b, t) = ∫_0^t ε_k^{γ²/2} e^{γ h_{ε_k}(b_s)} ds`
the approximating LQG clocks (`lqgClockApprox`) along a path `b`. If the occupation integrals of
the approximant densities along planar Brownian motion from `z`, stopped at `t ∧ τ`, `τ` the exit
time of a disc `B(0, r) ∋ z`, have expectation at most `C t^β` uniformly in the level, then

`sup_k P_z(A_k(·, t) ≥ η) → 0` as `t ↓ 0`, for every `η > 0`

(`tendsto_iSup_measure_le_lqgClockApprox_of_stopped_bound`): before `τ` the clock is the stopped
occupation integral, so Markov's inequality bounds `P_z(A_k(t) ≥ η, t < τ)` by `C t^β / η`, and
`P_z(τ ≤ t) → 0` because `τ` is almost surely finite (finite mean exit time of a bounded domain)
and positive (the path starts at `z` in the open disc).

For the dyadic approximants of the reference cone the stopped bound holds almost surely, for every
start, by the stopped heat bound; hence almost surely, for every start `z` and every `η > 0`, the
approximating clocks at time `t` are small in probability uniformly in the level as `t ↓ 0`
(`ae_coneRef_lqgClockApprox_small_initial`). This is the smallness hypothesis of the convergence
criterion "uniform convergence in measure from convergence after each positive time".
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set HarmonicBalls LQGMetric MarkovProcess
open Filter Topology Metric
open LatticeProb.LQG
open scoped ENNReal NNReal

namespace MatedCRT.FirstPass.Derived

/-- The real integral of an almost everywhere nonnegative function, as an extended nonnegative
real, is at most the lower Lebesgue integral of the function (with equality if it is
integrable; the left side is `0` otherwise). -/
theorem ofReal_integral_le_lintegral_ofReal_of_nonneg {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f) :
    ENNReal.ofReal (∫ a, f a ∂μ) ≤ ∫⁻ a, ENNReal.ofReal (f a) ∂μ := by
  by_cases hfi : Integrable f μ
  · rw [ofReal_integral_eq_lintegral_ofReal hfi hf]
  · rw [integral_undef hfi, ENNReal.ofReal_zero]
    exact zero_le

/-- **Small initial values of the approximating LQG clocks.** Let `ε_k ≥ 0` be scales at which
the circle averages `h_{ε_k}` are continuous, and `z ∈ B(0, r)`. If the occupation integrals of
the densities `ε_k^{γ²/2} e^{γ h_{ε_k}}` along planar Brownian motion from `z`, stopped at
`t ∧ τ_{B(0, r)}`, have expectation at most `C t^β` (`β > 0`) for every level `k` and time
`t ≥ 0`, then for every `η > 0`, `sup_k P_z(A_k(t) ≥ η) → 0` as `t ↓ 0`, where
`A_k(t) = ∫_0^t ε_k^{γ²/2} e^{γ h_{ε_k}(b_s)} ds`. -/
theorem tendsto_iSup_measure_le_lqgClockApprox_of_stopped_bound
    {γ : ℝ} {hε : ℝ → ℂ → ℝ} {ε : ℕ → ℝ} (hε0 : ∀ k, 0 ≤ ε k)
    (hcont : ∀ k, Continuous (hε (ε k))) {z : ℂ} {r β C : ℝ} (hz : z ∈ ball (0 : ℂ) r)
    (hβ : 0 < β)
    (hbound : ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t →
      ∫⁻ b, (∫⁻ s in Ioc 0 (min t (ContinuousPath.exitTime (ball (0 : ℂ) r) b).toReal),
          ENNReal.ofReal (ε k ^ (γ ^ 2 / 2) * Real.exp (γ * hε (ε k) (b s.toNNReal))))
        ∂(planarBrownianMotion z) ≤ ENNReal.ofReal (C * t ^ β))
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun t : ℝ≥0 => ⨆ k : ℕ,
      planarBrownianMotion z {b | η ≤ lqgClockApprox γ hε (ε k) b t}) (𝓝[>] 0) (𝓝 0) := by
  set Q := planarBrownianMotion z with hQ
  set τ : ContinuousPath ℂ → ℝ := fun b => (ContinuousPath.exitTime (ball (0 : ℂ) r) b).toReal
    with hτdef
  have hτm : Measurable τ :=
    ENNReal.measurable_toReal.comp (ContinuousPath.measurable_exitTime _ isOpen_ball)
  -- the exit time is almost surely finite and positive
  have hτpos : ∀ᵐ b ∂Q, 0 < τ b := by
    have hfin : ∀ᵐ b ∂Q, ContinuousPath.exitTime (ball (0 : ℂ) r) b < ⊤ :=
      ae_lt_top (ContinuousPath.measurable_exitTime _ isOpen_ball)
        (MatedCRT.KilledOccupation.lintegral_exitTime_planarBrownianMotion_lt_top isOpen_ball
          isBounded_ball z).ne
    filter_upwards [hfin, ae_planarBrownianMotion_eval_zero z] with b hb h0
    have hmem : b 0 ∈ ball (0 : ℂ) r := by rw [h0]; exact hz
    exact ENNReal.toReal_pos ((ContinuousPath.exitTime_pos_iff _ isOpen_ball b).2 hmem).ne' hb.ne
  have hseq := LatticeProb.MeasureLiminfTails.measure_le_inv_nat_tendsto_zero hτm.aemeasurable
    hτpos
  -- `P_z(τ ≤ t) → 0` as `t ↓ 0`
  have hτt : Tendsto (fun t : ℝ≥0 => Q {b | τ b ≤ (t : ℝ)}) (𝓝[>] 0) (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro e he
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((ENNReal.tendsto_nhds_zero.1 hseq) e he)
    let a : ℝ≥0 := ⟨1 / ((N : ℝ) + 1), by positivity⟩
    have ha : 0 < a := by
      change (0 : ℝ) < 1 / ((N : ℝ) + 1)
      positivity
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ha)] with t ht
    have ht' : (t : ℝ) ≤ 1 / ((N : ℝ) + 1) := le_of_lt (NNReal.coe_lt_coe.2 ht)
    exact (measure_mono fun b hb => le_trans hb ht').trans (hN N le_rfl)
  -- Markov's inequality before the exit time
  have hkey : ∀ t : ℝ≥0, ∀ k : ℕ, Q {b | η ≤ lqgClockApprox γ hε (ε k) b t} ≤
      Q {b | τ b ≤ (t : ℝ)} + ENNReal.ofReal (C * (t : ℝ) ^ β) / ENNReal.ofReal η := by
    intro t k
    set G : Set (ContinuousPath ℂ) := {b | (t : ℝ) < τ b} with hGdef
    have hG : MeasurableSet G := measurableSet_lt measurable_const hτm
    set Y : ContinuousPath ℂ → ℝ≥0∞ :=
      G.indicator (fun b => ENNReal.ofReal (lqgClockApprox γ hε (ε k) b t)) with hYdef
    have hYm : Measurable Y :=
      ((MatedCRT.measurable_lqgClockApprox (hcont k) t).ennreal_ofReal).indicator hG
    have hsub : {b | η ≤ lqgClockApprox γ hε (ε k) b t} ⊆
        {b | τ b ≤ (t : ℝ)} ∪ {b | ENNReal.ofReal η ≤ Y b} := by
      intro b hb
      by_cases hbG : b ∈ G
      · right
        change ENNReal.ofReal η ≤ Y b
        rw [hYdef, Set.indicator_of_mem hbG]
        exact ENNReal.ofReal_le_ofReal hb
      · left
        have hbG' : ¬ (t : ℝ) < τ b := hbG
        exact not_lt.1 hbG'
    have hYX : ∀ b, Y b ≤
        ∫⁻ s in Ioc 0 (min (t : ℝ) (ContinuousPath.exitTime (ball (0 : ℂ) r) b).toReal),
          ENNReal.ofReal (ε k ^ (γ ^ 2 / 2) * Real.exp (γ * hε (ε k) (b s.toNNReal))) := by
      intro b
      by_cases hbG : b ∈ G
      · have hlt : (t : ℝ) < (ContinuousPath.exitTime (ball (0 : ℂ) r) b).toReal := hbG
        rw [hYdef, Set.indicator_of_mem hbG, min_eq_left hlt.le, lqgClockApprox,
          intervalIntegral.integral_of_le t.coe_nonneg]
        exact ofReal_integral_le_lintegral_ofReal_of_nonneg
          (Eventually.of_forall fun s => mul_nonneg (Real.rpow_nonneg (hε0 k) _)
            (Real.exp_pos _).le)
      · have h0 : Y b = 0 := by simp [hYdef, hbG]
        rw [h0]
        exact zero_le
    have hmarkov : Q {b | ENNReal.ofReal η ≤ Y b} ≤ (∫⁻ b, Y b ∂Q) / ENNReal.ofReal η :=
      meas_ge_le_lintegral_div hYm.aemeasurable (ENNReal.ofReal_pos.2 hη).ne'
        ENNReal.ofReal_ne_top
    have hint : ∫⁻ b, Y b ∂Q ≤ ENNReal.ofReal (C * (t : ℝ) ^ β) :=
      (lintegral_mono hYX).trans (hbound k t t.coe_nonneg)
    calc Q {b | η ≤ lqgClockApprox γ hε (ε k) b t}
        ≤ Q ({b | τ b ≤ (t : ℝ)} ∪ {b | ENNReal.ofReal η ≤ Y b}) := measure_mono hsub
      _ ≤ Q {b | τ b ≤ (t : ℝ)} + Q {b | ENNReal.ofReal η ≤ Y b} := measure_union_le _ _
      _ ≤ Q {b | τ b ≤ (t : ℝ)} + ENNReal.ofReal (C * (t : ℝ) ^ β) / ENNReal.ofReal η :=
        add_le_add le_rfl (hmarkov.trans (ENNReal.div_le_div_right hint _))
  -- the bound tends to `0`
  have hu : Tendsto (fun t : ℝ≥0 => Q {b | τ b ≤ (t : ℝ)} +
      ENNReal.ofReal (C * (t : ℝ) ^ β) / ENNReal.ofReal η) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun t : ℝ≥0 => C * (t : ℝ) ^ β) (𝓝 0)
        (𝓝 (C * ((0 : ℝ≥0) : ℝ) ^ β)) :=
      (continuous_const.mul ((Real.continuous_rpow_const hβ.le).comp
        NNReal.continuous_coe)).tendsto 0
    rw [NNReal.coe_zero, Real.zero_rpow hβ.ne', mul_zero] at h0
    have h2 : Tendsto (fun t : ℝ≥0 => ENNReal.ofReal (C * (t : ℝ) ^ β)) (𝓝[>] 0) (𝓝 0) := by
      have := (ENNReal.tendsto_ofReal h0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ≥0)))
      rwa [ENNReal.ofReal_zero] at this
    have h3 := ENNReal.Tendsto.div_const h2 (Or.inr (ENNReal.ofReal_pos.2 hη).ne')
    have h4 := hτt.add h3
    rwa [ENNReal.zero_div, add_zero] at h4
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu (fun _ => zero_le)
    (fun t => iSup_le fun k => hkey t k)

/-- **Small initial values of the approximating clocks of the reference cone.** Almost surely, for
every path `w`-sample, every start `z` and every `η > 0`, the dyadic approximating LQG clocks
`A_k(t) = ∫_0^t ε^{γ²/2} e^{γ h_ε(b_s)} ds`, `ε = 2^{-k}`, of the reference cone built from
`c (Y ω)` and `w ω` satisfy `sup_k P_z(A_k(t) ≥ η) → 0` as `t ↓ 0`. -/
theorem ae_coneRef_lqgClockApprox_small_initial
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → DistC} (hY : IsNormalizedWPGFF Y P)
    {hC : DistC → (ℂ → ℝ) → ℝ} {c : DistC → ℝ → ℂ → ℝ}
    (hp : ∀ x (φ : TestC), hC x φ = x φ)
    (hc : ∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c (Y ω) r z = circleAvg (Y ω) r z)
    (hcont : ∀ x, ContinuousOn (fun p : ℝ × ℂ => c x p.1 p.2) (Ioi 0 ×ˢ univ))
    (hmeas : Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c q.2 q.1.1 q.1.2))
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (w : Ω → ContinuousPath ℝ) :
    ∀ᵐ ω ∂P, ∀ z : ℂ, ∀ η : ℝ, 0 < η →
      Tendsto (fun t : ℝ≥0 => ⨆ k : ℕ, planarBrownianMotion z
        {b | η ≤ lqgClockApprox γ (coneRefCircle γ (c (Y ω)) (w ω))
          (LatticeProb.LQG.dyadicScale k) b t}) (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [ae_coneRef_stopped_heat_bound hY hp hc hcont hmeas hγ hγ2 w]
    with ω hω z η hη
  obtain ⟨β, C, hβ, -, hb⟩ := hω (‖z‖ + 1) (by positivity)
  have hk : ∀ k, 0 < LatticeProb.LQG.dyadicScale k := fun k => by
    unfold LatticeProb.LQG.dyadicScale; positivity
  refine tendsto_iSup_measure_le_lqgClockApprox_of_stopped_bound (ε := LatticeProb.LQG.dyadicScale)
    (fun k => (hk k).le)
    (fun k => (continuousOn_coneRefCircle γ (hcont (Y ω)) (w ω)).comp_continuous
      (continuous_const.prodMk continuous_id) fun x => ⟨hk k, mem_univ _⟩)
    (mem_ball_zero_iff.2 (by linarith)) hβ (fun k t ht => hb z (by linarith) k t ht) hη

end MatedCRT.FirstPass.Derived
