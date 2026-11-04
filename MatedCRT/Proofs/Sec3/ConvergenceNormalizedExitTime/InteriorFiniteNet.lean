import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.NearPoleSmall
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.FiniteNetConvergence

/-! Interior convergence reduced to a finite-anchor estimate. -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory _root_.HarmonicBalls
open scoped ENNReal

/-- Pointwise convergence upgrades to convergence on a smaller closed ball
once both functions are approximated by finitely many common anchors. -/
theorem normalizedExitInterior_of_finite_anchors
    (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r r' : ℝ} {z : ℂ} (hr : 0 < r) (hr' : r' < r)
    (hball : ball z r ⊆ ball 0 ρ)
    (hnet : ∀ t : ℝ, 0 < t → ∀ e : ℝ≥0∞, 0 < e →
      ∃ K : Finset ℂ, (∀ x ∈ K, x ∈ closedBall z r') ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        S.P {ω | ∃ x ∈ closedBall z r', ∀ y ∈ K,
          t < |rescale (S.mε ε) ε (S.η ω)
              (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) x -
            rescale (S.mε ε) ε (S.η ω)
              (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) y| +
            |normalizedExitGreenPotential S r z ω x - normalizedExitGreenPotential S r z ω y|} ≤ e) :
    TendstoUniformlyOnInProbability S.P
      (fun ε ω => rescale (S.mε ε) ε (S.η ω)
        (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))))
      (normalizedExitGreenPotential S r z) (closedBall z r') := by
  apply uniformInProbability_of_finite_anchors S.P (closedBall z r') _ _ ?_ hnet
  intro x hx
  apply pointwise_normalizedExitTime_of_inputs 𝒮 h33 h35 h217 hγ hγ2 hρ hρ1 S hS hr hball
  exact (mem_ball).2 ((mem_closedBall.1 hx).trans_lt hr')

end MatedCRT
