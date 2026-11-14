import MatedCRT.Proofs.LBM.BrownianExitBall
import MarkovProcess.Path.Exhaustion

/-! # Simultaneous bounded-domain exits for planar Brownian motion -/

set_option autoImplicit false

open MeasureTheory Set Metric HarmonicBalls MarkovProcess
open scoped ENNReal

namespace MatedCRT

/-- For each starting point, almost every planar Brownian path exits every
bounded set in finite time, simultaneously over all bounded sets. -/
theorem ae_planarBrownianMotion_exit_all_bounded (y : ℂ) :
    ∀ᵐ b ∂planarBrownianMotion y, ∀ U : Set ℂ, Bornology.IsBounded U →
      ContinuousPath.exitTime U b < ⊤ := by
  have hexits : ∀ᵐ b ∂planarBrownianMotion y, ∀ n : ℕ,
      ContinuousPath.exitTime (ball (0 : ℂ) (n : ℝ)) b < ⊤ :=
    ae_all_iff.mpr (fun n => ae_planarBrownianMotion_exit_any_ball_lt_top y 0 n)
  filter_upwards [hexits] with b hb U hU
  obtain ⟨r, hr⟩ := hU.subset_ball (0 : ℂ)
  obtain ⟨n, hn⟩ := exists_nat_gt r
  exact lt_of_le_of_lt (ContinuousPath.exitTime_mono
    (hr.trans (ball_subset_ball (le_of_lt hn))) b) (hb n)

/-- In particular, almost every path exits all balls in finite time. -/
theorem ae_planarBrownianMotion_exit_all_balls (y : ℂ) :
    ∀ᵐ b ∂planarBrownianMotion y, ∀ (z : ℂ) (r : ℝ),
      ContinuousPath.exitTime (ball z r) b < ⊤ := by
  filter_upwards [ae_planarBrownianMotion_exit_all_bounded y] with b hb z r
  exact hb (ball z r) isBounded_ball

end MatedCRT
