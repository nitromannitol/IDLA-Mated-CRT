import MatedCRT.Proposed.Berestycki2015
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.KilledClockBridge
import HarmonicBalls.Proofs.Sec8.OpenBallDensity

/-! # Quenched identification of Dirichlet clock time changes -/

namespace MatedCRT

open HarmonicBalls MarkovProcess MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

universe u

/-- Compact containment makes all sufficiently fine Dirichlet circle-average
clocks measurable, uniformly in the stopping time parameter. -/
theorem IsDirichletGFF.ae_measurable_killedGMCClockApprox_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D U : Set ℂ}
    {h : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsDirichletGFF P D h hcirc) (hD : IsOpen D) (hU : IsOpen U)
    (hbounded : Bornology.IsBounded U) (hclosure : closure U ⊆ D) (γ : ℝ) (x : ℂ) :
    ∀ᵐ ω ∂P, ∃ N, ∀ n ≥ N, ∀ t, AEStronglyMeasurable
      (fun b => killedGMCClockApprox U γ (hcirc ω) (dyadicScale n) b t)
      (planarBrownianMotion x) := by
  obtain ⟨δ, hδ, hsub⟩ := hbounded.isCompact_closure.exists_cthickening_subset_open hD hclosure
  have hscale : ∀ᶠ n : ℕ in atTop, dyadicScale n < δ :=
    (tendsto_dyadicScale_nhdsGT.mono_right nhdsWithin_le_nhds).eventually (Iio_mem_nhds hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hscale
  filter_upwards [hgff.continuous_circle] with ω hcont
  refine ⟨N, fun n hn t => ?_⟩
  apply Measurable.aestronglyMeasurable
  apply measurable_killedGMCClockApprox_of_continuousOn hU γ (hcirc ω) (dyadicScale n) t
  apply hcont.comp (continuous_const.prodMk continuous_id).continuousOn
  intro z hz
  refine ⟨dyadicScale_pos n, ?_⟩
  intro w hw
  apply hsub
  apply Metric.mem_cthickening_of_dist_le w z δ (closure U) (subset_closure hz)
  exact (Metric.mem_closedBall.mp hw).trans (le_of_lt (hN n hn))

/-- A dyadic killed-clock limit is uniquely identified even when only a
tail of the approximations is measurable. -/
theorem IsLQGClock.ae_killed_clock_eq_all_of_ae_tendsto_tail
    {Q : Kernel ℂ (ContinuousPath ℂ)} {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    {x : ℂ} [IsFiniteMeasure (Q x)] {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hclock : IsLQGClock Q γ hε x F) (D : Set ℂ)
    {G : ContinuousPath ℂ → ℝ≥0 → ℝ} (N : ℕ)
    (hmeas : ∀ n ≥ N, ∀ t, AEStronglyMeasurable
      (fun b => killedGMCClockApprox D γ hε (dyadicScale n) b t) (Q x))
    (hG : ∀ t, ∀ᵐ b ∂Q x, Tendsto
      (fun n => killedGMCClockApprox D γ hε (dyadicScale n) b t) atTop (𝓝 (G b t)))
    (hcont : ∀ᵐ b ∂Q x, Continuous (G b) ∧ Continuous (F b)) :
    ∀ᵐ b ∂Q x, ∀ t, G b t =
      F b (min (t : ℝ≥0∞) (ContinuousPath.exitTime D b)).toNNReal := by
  obtain ⟨s, hs, hdense⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have heq : ∀ᵐ b ∂Q x, ∀ t ∈ s, G b t =
      F b (min (t : ℝ≥0∞) (ContinuousPath.exitTime D b)).toNNReal := by
    apply (ae_ball_iff hs).2
    intro t _
    have hshift : Tendsto (fun n : ℕ => n + N) atTop atTop :=
      tendsto_atTop_mono (fun n => Nat.le_add_right n N) tendsto_id
    have hG' : ∀ᵐ b ∂Q x, Tendsto
        (fun n => killedGMCClockApprox D γ hε (dyadicScale (n + N)) b t)
          atTop (𝓝 (G b t)) := by
      filter_upwards [hG t] with b hb
      exact hb.comp hshift
    have hm : ∀ n, AEStronglyMeasurable
        (fun b => killedGMCClockApprox D γ hε (dyadicScale (n + N)) b t) (Q x) :=
      fun n => hmeas (n + N) (Nat.le_add_left N n) t
    exact tendstoInMeasure_ae_unique (tendstoInMeasure_of_tendsto_ae hm hG')
      ((IsLQGClock.killed_tendstoInMeasure hclock D t).comp hshift)
  filter_upwards [heq, hcont] with b hb hc
  have h := hc.1.ext_on hdense (continuous_stopped_clock hc.2 _) hb
  intro t
  exact congrFun h t

/-- If the localized stopped-clock package holds, its path agrees with the
global LQG clock time change before exit. The package is an explicit hypothesis;
it is not supplied by the staged diffusion theorem. -/
theorem berestycki_dirichlet_time_change_eq_lbm
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D U : Set ℂ) (h : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (x : ℂ) (γ : ℝ) (F G : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hsource : ∀ᵐ q ∂(P.prod (planarBrownianMotion x)),
        let τ := ContinuousPath.exitTime U q.2
        let T := τ.toNNReal
        let K : ℕ → ℝ≥0 → ℝ := fun n =>
          killedGMCClockApprox U γ (hcirc q.1) (dyadicScale n) q.2
        τ < ⊤ ∧
        (∀ t : ℝ≥0, Tendsto (fun n => K n t) atTop (𝓝 (G q.1 q.2 t))) ∧
        Continuous (G q.1 q.2) ∧ G q.1 q.2 0 = 0 ∧
        StrictMonoOn (G q.1 q.2) (Set.Iic T) ∧
        (∀ t : ℝ≥0, T ≤ t → G q.1 q.2 t = G q.1 q.2 T) ∧
        (∀ t : ℝ≥0, (t : ℝ) < G q.1 q.2 T →
          Tendsto (fun n => q.2 ((killedClockInverse (K n) τ t).toNNReal))
            atTop (𝓝 (q.2 ((killedClockInverse (G q.1 q.2) τ t).toNNReal)))) ∧
        ContinuousOn (fun t : ℝ≥0 => q.2 ((killedClockInverse (G q.1 q.2) τ t).toNNReal))
          {t | (t : ℝ) < G q.1 q.2 T} ∧
        StrictMonoOn (fun t : ℝ≥0 => killedClockInverse (G q.1 q.2) τ t)
          {t | (t : ℝ) < G q.1 q.2 T})
    (hD : IsOpen D)
    (hU : IsOpen U) (hbounded : Bornology.IsBounded U) (hclosure : closure U ⊆ D)
    (hx : x ∈ U) (hgff : IsDirichletGFF P D h hcirc)
    (hglobal : ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ (hcirc ω) x (F ω) ∧
      ∀ᵐ b ∂planarBrownianMotion x, IsTimeChangeClock (F ω b)) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂planarBrownianMotion x,
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < lbmExitTime (F ω) U b →
          Tendsto (fun n => b ((killedClockInverse
            (killedGMCClockApprox U γ (hcirc ω) (dyadicScale n) b)
            (ContinuousPath.exitTime U b) t).toNNReal)) atTop
            (𝓝 (liouvilleBrownianPath (F ω) b t)) := by
  have hmeas := hgff.ae_measurable_killedGMCClockApprox_tail hD hU hbounded hclosure γ x
  filter_upwards [Measure.ae_ae_of_ae_prod hsource, hglobal, hmeas] with ω hsrc hg hm
  obtain ⟨N, hm⟩ := hm
  have hconv : ∀ t, ∀ᵐ b ∂planarBrownianMotion x, Tendsto
      (fun n => killedGMCClockApprox U γ (hcirc ω) (dyadicScale n) b t)
        atTop (𝓝 (G ω b t)) := by
    intro t
    filter_upwards [hsrc] with b hb
    exact hb.2.1 t
  have hcont : ∀ᵐ b ∂planarBrownianMotion x, Continuous (G ω b) ∧ Continuous (F ω b) := by
    filter_upwards [hsrc, hg.2] with b hb hf
    exact ⟨hb.2.2.1, hf.continuous⟩
  have hfin : ∀ᵐ b ∂planarBrownianMotion x, ContinuousPath.exitTime U b < ⊤ := by
    filter_upwards [hsrc] with b hb
    exact hb.1
  have heq := IsLQGClock.ae_killed_clock_eq_all_of_ae_tendsto_tail hg.1 U N hm hconv hcont
  have hreg : ∀ᵐ b ∂planarBrownianMotion x, IsTimeChangeClock (F ω b) ∧ b 0 ∈ U := by
    filter_upwards [hg.2, ae_planarBrownianMotion_eval_zero x] with b hb hstart
    exact ⟨hb, hstart ▸ hx⟩
  filter_upwards [hsrc, heq, hreg] with b hb he hr
  intro t ht
  have hval : G ω b (ContinuousPath.exitTime U b).toNNReal =
      F ω b (ContinuousPath.exitTime U b).toNNReal := by
    have hτ : ((ContinuousPath.exitTime U b).toNNReal : ℝ≥0∞) =
        ContinuousPath.exitTime U b := ENNReal.coe_toNNReal (ne_of_lt hb.1)
    simpa [hτ] using he (ContinuousPath.exitTime U b).toNNReal
  have hnonneg : 0 ≤ F ω b (ContinuousPath.exitTime U b).toNNReal := by
    simpa [hr.1.map_zero] using hr.1.strictMono.monotone
      (show 0 ≤ (ContinuousPath.exitTime U b).toNNReal from bot_le)
  have ht' : (t : ℝ) < G ω b (ContinuousPath.exitTime U b).toNNReal := by
    rw [lbmExitTime_eq_clockValue hU hr.1 hr.2 hb.1, ENNReal.coe_lt_coe] at ht
    have h := NNReal.coe_lt_coe.mpr ht
    simpa only [hval, Real.coe_toNNReal _ hnonneg] using h
  have hinv : killedClockInverse (G ω b) (ContinuousPath.exitTime U b) t =
      killedClockInverse (F ω b) (ContinuousPath.exitTime U b) t := by
    have hτ : ((ContinuousPath.exitTime U b).toNNReal : ℝ≥0∞) =
        ContinuousPath.exitTime U b := ENNReal.coe_toNNReal (ne_of_lt hb.1)
    rw [← hτ]
    apply killedClockInverse_eq_of_agree_before
    intro s hs
    have hs' : (s : ℝ≥0∞) ≤ ContinuousPath.exitTime U b := by
      rw [← hτ, ENNReal.coe_le_coe]
      exact hs
    simpa [min_eq_left hs'] using he s
  have hp : b ((killedClockInverse (G ω b) (ContinuousPath.exitTime U b) t).toNNReal) =
      liouvilleBrownianPath (F ω) b t := by
    rw [hinv]
    exact killedClockInverse_brownian_path_eq_lbm hU hr.1 hr.2 hb.1 ht
  simpa only [hp] using hb.2.2.2.2.2.2.1 t ht'

end MatedCRT
