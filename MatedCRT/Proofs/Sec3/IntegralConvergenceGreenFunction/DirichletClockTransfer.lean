import MatedCRT.Proposed.Berestycki2015
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.KilledClockBridge

/-! # Quenched identification of Dirichlet clock time changes -/

namespace MatedCRT

open HarmonicBalls MarkovProcess MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

universe u

/-- A localized Dirichlet-field dyadic construction, when its circle averages
also define the global LQG clock, converges to the latter's Liouville path
before exit for almost every field and Brownian path. -/
theorem berestycki_dirichlet_time_change_eq_lbm
    (hber : BerestyckiLiouvilleDiffusionStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D U : Set ℂ) (h : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (x : ℂ) (γ : ℝ) (F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hD : IsOpen D) (hproper : D ≠ univ) (hsimply : SimplyConnectedSpace D)
    (hU : IsOpen U) (hbounded : Bornology.IsBounded U) (hclosure : closure U ⊆ D)
    (hx : x ∈ U) (hgff : IsDirichletGFF P D h hcirc) (hγ : 0 ≤ γ) (hγ2 : γ < 2)
    (hglobal : ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ (hcirc ω) x (F ω) ∧
      ∀ᵐ b ∂planarBrownianMotion x, IsTimeChangeClock (F ω b))
    (hmeas : ∀ᵐ ω ∂P, ∀ n t, AEStronglyMeasurable
      (fun b => killedGMCClockApprox U γ (hcirc ω) (dyadicScale n) b t)
      (planarBrownianMotion x)) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂planarBrownianMotion x,
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < lbmExitTime (F ω) U b →
          Tendsto (fun n => b ((killedClockInverse
            (killedGMCClockApprox U γ (hcirc ω) (dyadicScale n) b)
            (ContinuousPath.exitTime U b) t).toNNReal)) atTop
            (𝓝 (liouvilleBrownianPath (F ω) b t)) := by
  obtain ⟨G, hsource⟩ := hber Ω P D U h hcirc x γ hD hproper hsimply hU
    hbounded hclosure hx hgff hγ hγ2
  filter_upwards [Measure.ae_ae_of_ae_prod hsource, hglobal, hmeas] with ω hsrc hg hm
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
  have heq := IsLQGClock.ae_killed_clock_eq_all_of_ae_tendsto hg.1 U hm hconv hcont
  have hreg : ∀ᵐ b ∂planarBrownianMotion x, IsTimeChangeClock (F ω b) ∧ b 0 ∈ U := by
    filter_upwards [hg.2, ae_planarBrownianMotion_eval_zero x] with b hb hstart
    exact ⟨hb, hstart ▸ hx⟩
  have hpath := IsLQGClock.ae_killed_inverse_path_eq_lbm_of_ae_tendsto
    hg.1 hU hm hconv hcont hfin hreg
  filter_upwards [hsrc, heq, hreg, hpath] with b hb he hr hp
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
  simpa only [hp t ht] using hb.2.2.2.2.2.2.1 t ht'

end MatedCRT
