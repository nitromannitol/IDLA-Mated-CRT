import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.LocalKernelBound
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.LocalKernelHarmonic
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.ProbabilitySubsequence

/-! # Almost-sure local Green-kernel estimates along a mesh subsequence -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- Any mesh sequence has a deterministic subsequence on which the local
boundedness and harmonicity prerequisites hold eventually almost surely. -/
theorem local_greenKernel_estimates_ae_subsequence (𝒮 : SpaceFillingSLEModel)
    (h214 : GreenKernelUpperBoundStmt 𝒮) {γ ρ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r d : ℝ} {z y : ℂ} {D : Set ℂ} (hr : 0 < r) (hd : 0 < d)
    (hball : ball z r ⊆ ball 0 ρ) (hy : dist y z + d < r)
    (hD : ∀ x ∈ D, dist x z + d < r) (hsep : ∀ x ∈ D, 4 * d ≤ dist y x)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] 0)) :
    ∃ K : ℝ, 0 < K ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
      ∀ᶠ n in atTop, ∀ b ∈ cellVertices (ε (φ n)) (S.η ω) D,
        |(ε (φ n))⁻¹ * greenKernel (S.mult (ε (φ n)) ω)
          (interiorCellVertices (ε (φ n)) (S.η ω) (ball z r))
          (vertexOf (ε (φ n)) (S.η ω) y) b| ≤ K / ε (φ n) ∧
        matedLaplacian (S.mult (ε (φ n)) ω)
          (fun a => (ε (φ n))⁻¹ * greenKernel (S.mult (ε (φ n)) ω)
            (interiorCellVertices (ε (φ n)) (S.η ω) (ball z r))
            (vertexOf (ε (φ n)) (S.η ω) y) a) b = 0 := by
  have hyball : y ∈ ball z r := by change dist y z < r; linarith
  have hDball : D ⊆ ball z r := by
    intro x hx
    change dist x z < r
    linarith [hD x hx]
  obtain ⟨K, hK, hbound⟩ := scaled_greenKernel_bound_on_separated_cells 𝒮 h214
    hγ hγ2 hρ hρ1 S hS hr hd hball hyball hDball hsep
  have hharm := scaled_greenKernel_harmonic_on_separated_cells 𝒮 hγ hγ2 S hS hd hball hy hD hsep
  obtain ⟨φ, hφ, hgood⟩ := exists_subseq_eventually_of_probTendsToOne S.P _
    (hbound.inter hharm) ε hε
  refine ⟨K, hK, φ, hφ, ?_⟩
  filter_upwards [hgood] with ω hω
  filter_upwards [hω] with n hn
  intro b hb
  exact ⟨hn.1 b hb, hn.2 b hb⟩

end MatedCRT
