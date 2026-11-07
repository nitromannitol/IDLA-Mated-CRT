import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.UniformAssembly
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.SeparateModuli

/-! # Compactness reduction for corrected harmonic convergence -/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- Pointwise Poisson convergence through the boundary. The boundary part is
supplied by the boundary-modulus argument of `LEMMA36-REPLACEMENT.md`,
lines 543–574. -/
def CorrectedPoissonPointwiseStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ ψ : ℂ → ℝ, ContinuousOn ψ (closedBall z r) → ∀ y ∈ closedBall z r,
    TendstoInProbability S.P (fun ε ω => projectedDiscreteHarmonicExtension S r z ψ ε ω y)
      (fun _ => discPoissonExtension ψ z r y)

/-- Asymptotic equicontinuity in probability for projected discrete harmonic
extensions on the closed disc, including the boundary cells. See
`LEMMA36-REPLACEMENT.md`, lines 491–574. -/
def CorrectedHarmonicModulusStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ ψ : ℂ → ℝ, ContinuousOn ψ (closedBall z r) →
  ∀ t : ℝ, 0 < t → ∀ e : ℝ≥0∞, 0 < e → ∃ δ : ℝ, 0 < δ ∧
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | ∃ x ∈ closedBall z r, ∃ y ∈ closedBall z r,
      dist x y < δ ∧ |projectedDiscreteHarmonicExtension S r z ψ ε ω x -
        projectedDiscreteHarmonicExtension S r z ψ ε ω y| > t} ≤ e

/-- Pointwise convergence and the discrete modulus give the uniform Poisson
step, using compactness of the disc and continuity of its Poisson extension. -/
theorem correctedPoissonUniform_of_modulus (𝒮 : SpaceFillingSLEModel)
    (hpoint : CorrectedPoissonPointwiseStep 𝒮) (hmod : CorrectedHarmonicModulusStep 𝒮) :
    CorrectedPoissonUniformStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ hψ
  apply uniformInProbability_of_separate_moduli S.P (closedBall z r) (isCompact_closedBall z r)
    (projectedDiscreteHarmonicExtension S r z ψ) (fun _ => discPoissonExtension ψ z r)
    (hpoint γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ hψ)
    (hmod γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ hψ)
  intro t ht e he
  have hc := continuousOn_discPoissonExtension hr (hψ.mono sphere_subset_closedBall)
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_closedBall z r).uniformContinuousOn_of_continuous hc) t ht
  refine ⟨δ, hδ, ?_⟩
  have hempty : {ω : Ω | ∃ x ∈ closedBall z r, ∃ y ∈ closedBall z r,
      dist x y < δ ∧ t < |discPoissonExtension ψ z r x - discPoissonExtension ψ z r y|} = ∅ := by
    ext ω
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨x, hx, y, hy, hxy, hbad⟩
    have h := hδu x hx y hy hxy
    rw [Real.dist_eq] at h
    linarith
  rw [hempty, measure_empty]
  exact zero_le

end MatedCRT
