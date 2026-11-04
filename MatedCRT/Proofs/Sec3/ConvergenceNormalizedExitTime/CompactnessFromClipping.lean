import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.ExitModulus

/-! Application of discrete potential tightness to clipped exit times. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology

/-- Discrete potential tightness applies to an admissible sequence that is
eventually equal almost surely to the normalized exit time. -/
theorem exit_compactness_of_admissible_approximations
    (𝒮 : SpaceFillingSLEModel) (h31 : DiscretePotentialTightnessStmt 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (D : Set ℂ) (hD : D ⊆ ball 0 ρ) (hconn : IsConnected D)
    (K : Set ℂ) (hK : IsCompact K) (hKD : closure K ⊆ D)
    (E : Ω → ℕ → ℝ) (v : Ω → ℕ → ℤ → ℝ) (C : Ω → ℝ)
    (hEm : ∀ n, Measurable[S.envSigma] fun ω => E ω n)
    (hEpos : ∀ ω n, 0 < E ω n) (hElim : ∀ ω, Tendsto (E ω) atTop (𝓝 0))
    (hvm : ∀ n a, Measurable[S.envSigma] fun ω => v ω n a)
    (hCm : Measurable[S.envSigma] C) (hCpos : ∀ ω, 0 < C ω)
    (hlap : ∀ ω n, ∀ a ∈ interiorCellVertices (E ω n) (S.η ω) D,
      |matedLaplacian (S.mult (E ω n) ω) (v ω n) a| ≤ C ω)
    (hsize : ∀ ω n, ∀ a ∈ cellVertices (E ω n) (S.η ω) D,
      |v ω n a| ≤ C ω / E ω n)
    (heq : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      v ω n = normExitTime (S.mult (E ω n) ω)
        (interiorCellVertices (E ω n) (S.η ω) D)) :
    ∀ᵐ ω ∂S.P, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u : ℂ → ℝ,
      ContinuousOn u K ∧ TendstoUniformlyOn
        (fun k => rescale (S.mε (E ω (φ k))) (E ω (φ k)) (S.η ω)
          (normExitTime (S.mult (E ω (φ k)) ω)
            (interiorCellVertices (E ω (φ k)) (S.η ω) D))) u atTop K := by
  obtain ⟨Φ, hΦm, hΦ⟩ := h31 γ hγ hγ2 ρ hρ hρ1 Ω S hS D hD hconn E v C
    hEm hEpos hElim hvm hCm hCpos hlap hsize
  filter_upwards [hΦ, heq] with ω hω hv
  obtain ⟨hmono, u, hu, hconv, hboundary⟩ := hω
  refine ⟨Φ ω, hmono, u, hu.mono ?_, ?_⟩
  · exact subset_closure.trans hKD
  · have ht := hconv K hK hKD
    apply ht.congr
    filter_upwards [hmono.tendsto_atTop.eventually hv] with n hn
    intro x hx
    rw [hn]

end MatedCRT
