import MatedCRT.Defs.KilledGMCClock
import MatedCRT.Proofs.LBM.ExitTimeChange

/-! # Inverses of stopped Liouville clocks -/

namespace MatedCRT

open HarmonicBalls MarkovProcess Set
open scoped ENNReal NNReal

/-- Clipping the inverse at `T` makes it depend only on the clock up to `T`.
No monotonicity or continuity is needed, so this also applies to the circle
average approximations before their convergence has been established. -/
theorem killedClockInverse_eq_of_agree_before {F G : ℝ≥0 → ℝ} {T t : ℝ≥0}
    (h : ∀ s ≤ T, F s = G s) :
    killedClockInverse F T t = killedClockInverse G T t := by
  apply le_antisymm
  all_goals
    unfold killedClockInverse
    apply le_min (min_le_left _ _)
    apply le_iInf
    intro s
    apply le_iInf
    intro hs
    by_cases hst : s ≤ T
    · apply (min_le_right _ _).trans
      apply iInf_le_of_le s
      apply iInf_le
      simpa only [h s hst] using hs
    · exact (min_le_left _ _).trans (by exact_mod_cast (le_of_not_ge hst))

/-- If the clock eventually exceeds the target time, the killed inverse is
the ordinary right-continuous inverse stopped at the killing time. -/
theorem killedClockInverse_eq_min_clockInverse {F : ℝ≥0 → ℝ} {τ : ℝ≥0∞} {t : ℝ≥0}
    (h : ∃ s, (t : ℝ) < F s) :
    killedClockInverse F τ t = min τ (clockInverse F t : ℝ≥0∞) := by
  unfold killedClockInverse clockInverse
  exact congrArg (min τ) (ENNReal.coe_sInf h).symm

/-- Before its terminal clock time, a killed global time-change clock has
exactly the same inverse as the unrestricted clock. -/
theorem killedClockInverse_eq_clockInverse_before_exit {F : ℝ≥0 → ℝ}
    {τ : ℝ≥0∞} {t : ℝ≥0} (hF : IsTimeChangeClock F) (hτ : τ < ⊤)
    (ht : (t : ℝ) < F τ.toNNReal) :
    killedClockInverse F τ t = (clockInverse F t : ℝ≥0∞) := by
  have hFnonneg : 0 ≤ F τ.toNNReal := by
    simpa [hF.map_zero] using hF.strictMono.monotone (show 0 ≤ τ.toNNReal from bot_le)
  have hq : t < Real.toNNReal (F τ.toNNReal) := by
    apply NNReal.coe_lt_coe.mp
    simpa only [Real.coe_toNNReal _ hFnonneg] using ht
  have hinv : clockInverse F t < τ.toNNReal := by
    rw [← clockInverse_clockValue hF.map_zero hF.strictMono τ.toNNReal]
    exact IsTimeChangeClock.strictMono_clockInverse hF hq
  rw [killedClockInverse_eq_min_clockInverse ⟨τ.toNNReal, ht⟩]
  apply min_eq_right
  rw [← ENNReal.coe_toNNReal (ne_of_lt hτ), ENNReal.coe_le_coe]
  exact hinv.le

/-- Before Brownian exit the killed approximating clock has the same stopped
inverse as the unrestricted circle-average clock. -/
theorem killedGMCClockApprox_inverse_eq (D : Set ℂ) (γ : ℝ)
    (hε : ℝ → ℂ → ℝ) (ε : ℝ) (b : ContinuousPath ℂ)
    (hfin : ContinuousPath.exitTime D b < ⊤) (t : ℝ≥0) :
    killedClockInverse (killedGMCClockApprox D γ hε ε b)
        (ContinuousPath.exitTime D b) t =
      killedClockInverse (lqgClockApprox γ hε ε b)
        (ContinuousPath.exitTime D b) t := by
  have hτ : ((ContinuousPath.exitTime D b).toNNReal : ℝ≥0∞) =
      ContinuousPath.exitTime D b := ENNReal.coe_toNNReal (ne_of_lt hfin)
  rw [← hτ]
  apply killedClockInverse_eq_of_agree_before
  intro s hs
  apply killedGMCClockApprox_eq_before_exit
  rw [← hτ, ENNReal.coe_le_coe]
  exact hs

end MatedCRT
