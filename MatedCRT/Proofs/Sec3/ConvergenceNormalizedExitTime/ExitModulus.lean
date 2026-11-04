import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.ModulusFromVersions
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.OscillationMeasurable
import MatedCRT.Proofs.Measurability.EnvSigma
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.InteriorDiscreteModulus

/-! Exit-time moduli from random subsequential compactness. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- Random subsequential compactness of the rescaled exit times implies a
probabilistic spatial modulus on a compact set. -/
theorem MatedCRTEnv.IsValid.exit_modulus_of_random_compactness
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (D : Set ℂ) (hD : IsOpen D ∨ IsClosed D) (K : Set ℂ) (hK : IsCompact K)
    (hcompact : ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ I : Ω → ℕ → ℕ,
      (∀ n, Measurable[S.envSigma] fun ω => I ω n) → (∀ ω n, n ≤ I ω n) →
      ∀ᵐ ω ∂S.P, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u : ℂ → ℝ,
        ContinuousOn u K ∧ TendstoUniformlyOn
          (fun k => rescale (S.mε (ε (ψ (I ω (φ k))))) (ε (ψ (I ω (φ k)))) (S.η ω)
            (normExitTime (S.mult (ε (ψ (I ω (φ k)))) ω)
              (interiorCellVertices (ε (ψ (I ω (φ k)))) (S.η ω) D))) u atTop K)
    {t : ℝ} (ht : 0 < t) {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < δ ∧ t < |rescale (S.mε ε) ε (S.η ω)
          (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) D)) x -
        rescale (S.mε ε) ε (S.η ω)
          (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) D)) y|} ≤ e := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  apply mesh_modulus_of_random_compactness_versions S.P S.envSigma K hK _ t ht ?_ hcompact he
  intro ε hε δ
  obtain ⟨A, hAm, hAe⟩ := hS.exists_envSigma_measurable_exit_oscillation ε hε D hD K hK δ t
  exact ⟨A, hAm, hS.nullMeasurableSet_of_envSigma hAm, hAe⟩

/-- Pointwise convergence and random subsequential compactness yield uniform
convergence in probability on a smaller closed ball. -/
theorem normalizedExitInterior_of_random_compactness
    (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r r' : ℝ} {z : ℂ} (hr : 0 < r) (hr' : r' < r)
    (hball : ball z r ⊆ ball 0 ρ)
    (hcompact : ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ I : Ω → ℕ → ℕ,
      (∀ n, Measurable[S.envSigma] fun ω => I ω n) → (∀ ω n, n ≤ I ω n) →
      ∀ᵐ ω ∂S.P, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u : ℂ → ℝ,
        ContinuousOn u (closedBall z r') ∧ TendstoUniformlyOn
          (fun k => rescale (S.mε (ε (ψ (I ω (φ k))))) (ε (ψ (I ω (φ k)))) (S.η ω)
            (normExitTime (S.mult (ε (ψ (I ω (φ k)))) ω)
              (interiorCellVertices (ε (ψ (I ω (φ k)))) (S.η ω) (ball z r))))
          u atTop (closedBall z r')) :
    TendstoUniformlyOnInProbability S.P
      (fun ε ω => rescale (S.mε ε) ε (S.η ω)
        (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))))
      (normalizedExitGreenPotential S r z) (closedBall z r') := by
  apply normalizedExitInterior_of_discrete_modulus 𝒮 h33 h35 h217 hγ hγ2 hρ hρ1
    S hS hr hr' hball
  intro t ht e he
  exact hS.exit_modulus_of_random_compactness (ball z r) (Or.inl isOpen_ball)
    (closedBall z r') (isCompact_closedBall _ _) hcompact ht he

end MatedCRT
