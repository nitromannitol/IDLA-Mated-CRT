import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.KilledClockConvergence
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.KilledClockInverse

/-! # Identification of killed clock inverses -/

namespace MatedCRT

open HarmonicBalls MarkovProcess MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

/-- A continuous dyadic killed-clock limit has the same stopped inverse as
the global LQG clock, simultaneously at every clock time. -/
theorem IsLQGClock.ae_killed_inverse_eq_of_ae_tendsto
    {Q : Kernel ℂ (ContinuousPath ℂ)} {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    {x : ℂ} [IsFiniteMeasure (Q x)] {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hclock : IsLQGClock Q γ hε x F) (D : Set ℂ)
    {G : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hmeas : ∀ n t, AEStronglyMeasurable
      (fun b => killedGMCClockApprox D γ hε (dyadicScale n) b t) (Q x))
    (hG : ∀ t, ∀ᵐ b ∂Q x, Tendsto
      (fun n => killedGMCClockApprox D γ hε (dyadicScale n) b t) atTop (𝓝 (G b t)))
    (hcont : ∀ᵐ b ∂Q x, Continuous (G b) ∧ Continuous (F b))
    (hfin : ∀ᵐ b ∂Q x, ContinuousPath.exitTime D b < ⊤) :
    ∀ᵐ b ∂Q x, ∀ t, killedClockInverse (G b) (ContinuousPath.exitTime D b) t =
      killedClockInverse (F b) (ContinuousPath.exitTime D b) t := by
  filter_upwards [IsLQGClock.ae_killed_clock_eq_all_of_ae_tendsto hclock D hmeas hG hcont, hfin]
    with b heq hb
  intro t
  have hτ : ((ContinuousPath.exitTime D b).toNNReal : ℝ≥0∞) =
      ContinuousPath.exitTime D b := ENNReal.coe_toNNReal (ne_of_lt hb)
  rw [← hτ]
  apply killedClockInverse_eq_of_agree_before
  intro s hs
  have hs' : (s : ℝ≥0∞) ≤ ContinuousPath.exitTime D b := by
    rw [← hτ, ENNReal.coe_le_coe]
    exact hs
  simpa [min_eq_left hs'] using heq s

/-- Before Liouville exit, the path driven by the killed-clock limit agrees
with the unrestricted Liouville Brownian path. -/
theorem IsLQGClock.ae_killed_inverse_path_eq_lbm_of_ae_tendsto
    {Q : Kernel ℂ (ContinuousPath ℂ)} {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    {x : ℂ} [IsFiniteMeasure (Q x)] {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hclock : IsLQGClock Q γ hε x F) {D : Set ℂ} (hD : IsOpen D)
    {G : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hmeas : ∀ n t, AEStronglyMeasurable
      (fun b => killedGMCClockApprox D γ hε (dyadicScale n) b t) (Q x))
    (hG : ∀ t, ∀ᵐ b ∂Q x, Tendsto
      (fun n => killedGMCClockApprox D γ hε (dyadicScale n) b t) atTop (𝓝 (G b t)))
    (hcont : ∀ᵐ b ∂Q x, Continuous (G b) ∧ Continuous (F b))
    (hfin : ∀ᵐ b ∂Q x, ContinuousPath.exitTime D b < ⊤)
    (hregular : ∀ᵐ b ∂Q x, IsTimeChangeClock (F b) ∧ b 0 ∈ D) :
    ∀ᵐ b ∂Q x, ∀ t : ℝ≥0, (t : ℝ≥0∞) < lbmExitTime F D b →
      b ((killedClockInverse (G b) (ContinuousPath.exitTime D b) t).toNNReal) =
        liouvilleBrownianPath F b t := by
  filter_upwards [IsLQGClock.ae_killed_inverse_eq_of_ae_tendsto hclock D hmeas hG hcont hfin,
    hfin, hregular] with b hinv hb hr
  intro t ht
  rw [hinv t]
  exact killedClockInverse_brownian_path_eq_lbm hD hr.1 hr.2 hb ht

end MatedCRT
