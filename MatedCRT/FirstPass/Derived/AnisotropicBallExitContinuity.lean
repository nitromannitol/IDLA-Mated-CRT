import MatedCRT.FirstPass.Derived.AnisotropicRegularExit
import MatedCRT.FirstPass.Derived.JointBallExitContinuity

/-! # Ball exit continuity for linear images of planar Brownian motion -/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

/-- Linear images of planar Brownian motion leave positive balls regularly. -/
theorem ae_regularExit_ball_linearImage_planarBrownian (L : ℂ ≃L[ℝ] ℂ)
    {x : ℂ} {r : ℝ} (hr : 0 < r) (hx : L x ∈ ball (0 : ℂ) r) :
    ∀ᵐ b ∂planarBrownianMotion x,
      pathExitTime (ball (0 : ℂ) r) (fun t => L (b t)) ≠ ⊤ ∧
        MatedCRT.TruncatedLaws.RegularExit (ball (0 : ℂ) r) (fun t => L (b t)) := by
  apply ae_regularExit_linearImage_planarBrownian L isOpen_ball (isBounded_ball) measurable_id ?_ hx
  intro p hp
  have hp' : p ∈ sphere (0 : ℂ) r := frontier_ball_subset_sphere hp
  have hp0 : p ≠ 0 := by
    intro heq
    subst p
    have h : (0 : ℝ) = r := by simpa [mem_sphere] using hp'
    linarith
  refine ⟨hp0, ?_⟩
  intro q hq
  have hq' : 0 < inner ℝ (p - (0 : ℂ)) (q - p) := by simpa using hq
  exact fun h => MatedCRT.not_mem_closedBall_of_inner_sub_pos hp' hq'
    (closure_ball_subset_closedBall h)

/-- For a linear image of planar Brownian motion, the ball exit time is almost
surely jointly continuous in the path and positive radius. -/
theorem ae_continuousAt_ball_exitTime_linearImage_planarBrownian (L : ℂ ≃L[ℝ] ℂ)
    {x : ℂ} {r : ℝ} (hr : 0 < r) (hx : L x ∈ ball (0 : ℂ) r) :
    ∀ᵐ b ∂planarBrownianMotion x,
      ContinuousAt (fun p : ContinuousPath ℂ × ℝ =>
        ContinuousPath.exitTime (ball (0 : ℂ) p.2) p.1)
        (((⟨L, L.continuous⟩ : C(ℂ, ℂ)).comp b), r) := by
  filter_upwards [ae_regularExit_ball_linearImage_planarBrownian L hr hx] with b hb
  exact continuousAt_planarBall_exitTime_joint hr hb.1 (hb.2.resolve_left hb.1)

end MatedCRT.StopAtExitCmp
