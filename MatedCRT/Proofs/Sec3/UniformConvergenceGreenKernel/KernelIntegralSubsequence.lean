import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.UniversalCutoff
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.SmoothTests
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.LocalKernelBound
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapProbability
import MatedCRT.Steps.Sec4.ObstacleSpecialization

/-! # Green-kernel integral convergence along a subsequence -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls
open scoped ContDiff

/-- For a fixed smooth test supported inside the ball, a deterministic mesh
subsequence gives almost-sure convergence of the degree-weighted kernel integral. -/
theorem green_kernel_integral_ae_subsequence (𝒮 : SpaceFillingSLEModel)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) {γ ρ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z y : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    (hy : y ∈ ball z r) (f : ℂ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (hfball : tsupport f ⊆ ball z r)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] 0)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ᵐ sample ∂S.P,
      Tendsto (fun n => ∫ x, f x * rescale (S.mε (ε (ψ n))) (ε (ψ n)) (S.η sample)
        (fun b => (ε (ψ n))⁻¹ * greenKernel (S.mult (ε (ψ n)) sample)
          (interiorCellVertices (ε (ψ n)) (S.η sample) (ball z r))
          (vertexOf (ε (ψ n)) (S.η sample) y) b) x
        ∂degreeWeightedMeasure (S.mult (ε (ψ n)) sample) (ε (ψ n)) (S.η sample) (S.μ sample))
        atTop (𝓝 (S.c₀ * ∫ x in ball z r, greenFunction (ball z r) y x * f x ∂S.μ sample)) := by
  obtain ⟨φ, hφs, hφc, hconv⟩ := GreenEnvironment.exists_cutoff_for_integral_convergence
    (isBounded_ball : Bornology.IsBounded (ball z r)) hf.continuous hfc hfball
  obtain ⟨ψ, hψ, hlim⟩ := exists_subseq_ae_of_two_tendstoInProbability S.P
    (integralConvergenceGreenFunction_smooth_test 𝒮 h34 hγ hγ2 hρ hρ1 S hS hr hball hy f hf hfc)
    (integralConvergenceGreenFunction_smooth_test 𝒮 h34 hγ hγ2 hρ hρ1 S hS hr hball hy φ hφs hφc)
    ε hε
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [hlim, hS.isAreaParametrized, hS.ae_tendsto_cocompact,
    hS.isLQGMeasure, hS.ae_isLocallyFiniteMult hγ hγ2 (adjacentCellsMeetAeStep 𝒮)]
      with sample hlimsample hη hp hμ hlf
  let : IsLocallyFiniteMeasure (S.μ sample) := hμ.isLocallyFiniteMeasure
  have hε' : Tendsto (fun n => ε (ψ n)) atTop (𝓝[>] 0) := hε.comp hψ.tendsto_atTop
  have hpos : ∀ᶠ n in atTop, 0 < ε (ψ n) := hε'.eventually self_mem_nhdsWithin
  apply hconv (S.μ sample) (S.η sample) hη hp (fun n => ε (ψ n))
    (fun n => S.mε (ε (ψ n))) (fun n => S.mult (ε (ψ n)) sample)
    (fun n => interiorCellVertices (ε (ψ n)) (S.η sample) (ball z r))
    (fun n => vertexOf (ε (ψ n)) (S.η sample) y) hε' ?_ _ _ hlimsample.1 hlimsample.2
  filter_upwards [hpos] with n hn
  refine ⟨medianOf_nonneg _, ?_⟩
  intro b hb
  exact (mdeg_pos_of_ne_zero (hlf _ hn) (S.mult_succ_ne_zero hn.le sample b)).ne'

end MatedCRT
