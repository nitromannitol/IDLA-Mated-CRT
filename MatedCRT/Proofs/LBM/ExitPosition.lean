import MatedCRT.Proofs.LBM.BrownianExitBall
import MatedCRT.Proofs.LBM.TimeChangeContinuity

/-! Boundary values of continuous time-changed Brownian paths. -/

namespace MatedCRT

open MeasureTheory Set Filter Topology HarmonicBalls MarkovProcess Metric
open scoped ENNReal NNReal

/-- A continuous path started in an open set reaches its frontier at a finite exit time. -/
theorem pathExitPosition_mem_frontier_of_continuous {U : Set ℂ} (hU : IsOpen U)
    {f : ℝ≥0 → ℂ} (hf : Continuous f) (h0 : f 0 ∈ U)
    (hfin : pathExitTime U f < ⊤) : pathExitPosition U f ∈ frontier U := by
  let p : ContinuousPath ℂ := ⟨f, hf⟩
  have ht : ContinuousPath.exitTime U p = pathExitTime U f := rfl
  have hp := ContinuousPath.coordinate_exitTime_mem_frontier U hU p h0 (by
    rw [ht]
    exact ne_of_lt hfin)
  change f ((ContinuousPath.exitTime U p).toNNReal) ∈ frontier U at hp
  simpa only [pathExitPosition, ← ht, ContinuousPath.untopD_exitTime] using hp

/-- Normalized Liouville Brownian motion exits a ball at its boundary almost surely. -/
theorem MatedCRTEnv.IsValid.ae_normalizedLBMExitPosition_mem_sphere
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ)
    {y z : ℂ} {r : ℝ} (hy : y ∈ ball z r) :
    ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y,
      pathExitPosition (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b) ∈ sphere z r := by
  filter_upwards [hS.isLQGClock,
    hS.ae_normalizedLBMExitTime_any_ball_lt_top hγ hγ2 y z r] with ω hc hfinite
  filter_upwards [(hc y).2, ae_planarBrownianMotion_eval_zero y, hfinite] with b hclock hstart hfin
  apply frontier_ball_subset_sphere
  apply pathExitPosition_mem_frontier_of_continuous isOpen_ball
    (continuous_rescaledLBMPath hclock) ?_ hfin
  have hI : clockInverse (S.clock ω b) 0 = 0 := by
    have h := clockInverse_clockValue hclock.map_zero hclock.strictMono 0
    simpa only [hclock.map_zero, Real.toNNReal_zero] using h
  simpa only [rescaledLBMPath, mul_zero, liouvilleBrownianPath, hI, hstart] using hy

end MatedCRT
