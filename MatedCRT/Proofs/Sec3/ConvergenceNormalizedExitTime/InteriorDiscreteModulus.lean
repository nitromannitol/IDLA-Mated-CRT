import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.PointwiseModulusProbability
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.PotentialContinuous
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.InteriorFiniteNet
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.SeparateModuli

/-! Reduction of interior convergence to a discrete modulus estimate. -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory _root_.HarmonicBalls
open scoped ENNReal

/-- The continuum Green potential has a probabilistic modulus on each smaller
closed ball. -/
theorem normalizedExitGreenPotential_modulus_small
    (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r r' : ℝ} {z : ℂ} (hr : 0 < r) (hr' : r' < r)
    (hball : ball z r ⊆ ball 0 ρ) {t : ℝ} (ht : 0 < t)
    {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ S.P {ω | ∃ x ∈ closedBall z r', ∃ y ∈ closedBall z r',
      dist x y < δ ∧ t < |normalizedExitGreenPotential S r z ω x -
        normalizedExitGreenPotential S r z ω y|} ≤ e := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  apply pointwiseMeasurable_modulus_small_in_probability S.P (closedBall z r')
    (isCompact_closedBall z r') (normalizedExitGreenPotential S r z) ?_ ?_ ht he
  · intro x hx
    apply normalizedExitGreenPotential_aemeasurable 𝒮 h33 h217 hγ hγ2 hρ hρ1 S hS hr hball
    exact (mem_ball).2 ((mem_closedBall.1 hx).trans_lt hr')
  · filter_upwards [normalizedExitGreenPotential_ae_continuousOn 𝒮 h217 hγ hγ2 hρ hρ1
      S hS hr hball] with ω hc
    exact hc.mono (closedBall_subset_closedBall hr'.le)

/-- Pointwise convergence and a probabilistic modulus for the discrete exit
times imply uniform interior convergence in probability. -/
theorem normalizedExitInterior_of_discrete_modulus
    (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r r' : ℝ} {z : ℂ} (hr : 0 < r) (hr' : r' < r)
    (hball : ball z r ⊆ ball 0 ρ)
    (hmod : ∀ t : ℝ, 0 < t → ∀ e : ℝ≥0∞, 0 < e → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | ∃ x ∈ closedBall z r', ∃ y ∈ closedBall z r',
        dist x y < δ ∧ t < |rescale (S.mε ε) ε (S.η ω)
          (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) x -
          rescale (S.mε ε) ε (S.η ω)
          (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) y|} ≤ e) :
    TendstoUniformlyOnInProbability S.P
      (fun ε ω => rescale (S.mε ε) ε (S.η ω)
        (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))))
      (normalizedExitGreenPotential S r z) (closedBall z r') := by
  apply uniformInProbability_of_separate_moduli S.P (closedBall z r') (isCompact_closedBall z r') _ _
  · intro x hx
    apply pointwise_normalizedExitTime_of_inputs 𝒮 h33 h35 h217 hγ hγ2 hρ hρ1 S hS hr hball
    exact (mem_ball).2 ((mem_closedBall.1 hx).trans_lt hr')
  · exact hmod
  · intro t ht e he
    exact normalizedExitGreenPotential_modulus_small 𝒮 h33 h217 hγ hγ2 hρ hρ1 S hS hr hr'
      hball ht he

end MatedCRT
