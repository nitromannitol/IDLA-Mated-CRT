import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.CompactCover
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.PathwiseRelativeCompactness

/-! # Measurable local selection after deterministic preparation -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- The prepared pathwise step yields measurable local selection for each
    family of admissible data, on an almost-sure event depending on that family. -/
theorem preparedTightness_ae_measurable_local (𝒮 : SpaceFillingSLEModel)
    (hp : PreparedTightnessPathwiseStep 𝒮) {γ ρ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ A : Set Ω, (∀ᵐ ω ∂S.P, ω ∈ A) ∧
      ∀ (D : ℕ → Set ℂ), (∀ j, D j ⊆ ball 0 ρ ∧ IsOpen (D j) ∧ IsConnected (D j)) →
      ∀ (E : Ω → ℕ → ℝ) (u : ℕ → Ω → ℕ → ℤ → ℝ) (C : ℕ → Ω → ℝ),
        (∀ n, Measurable[S.envSigma] fun ω => E ω n) →
        (∀ ω n, E ω n ∈ range (e ∘ φ)) → (∀ ω, Tendsto (E ω) atTop (𝓝 0)) →
        (∀ j n a, Measurable[S.envSigma] fun ω => u j ω n a) →
        (∀ j, Measurable[S.envSigma] (C j)) →
        ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
          ∀ᵐ ω ∂S.P, StrictMono (Φ ω) ∧
            (ω ∈ A → PreparedTightnessBounds S D E u C ω →
              ∀ j, ∃ v : ℂ → ℝ, ContinuousOn v (D j) ∧
                ∀ O, IsCompact O → O ⊆ D j → TendstoUniformlyOn
                  (fun n => rescale (S.mε (E ω (Φ ω n))) (E ω (Φ ω n))
                    (S.η ω) (u j ω (Φ ω n))) v atTop O) := by
  obtain ⟨φ, hφ, A, hA, hpath⟩ := preparedTightness_relative_compactness 𝒮 hp
    hγ hγ2 hρ hρ1 S hS e he he0
  refine ⟨φ, hφ, A, hA, ?_⟩
  intro D hD E u C hEm hEr hE0 hum hCm
  let P : Ω → Prop := fun ω => ω ∈ A ∧ PreparedTightnessBounds S D E u C ω
  have hc : ∀ᵐ ω ∂S.P, P ω → ∀ j O, IsCompact O → O ⊆ D j →
      ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ θ : ℕ → ℕ, StrictMono θ ∧
        ∃ w : ℂ → ℝ, ContinuousOn w O ∧ TendstoUniformlyOn
          (fun n => rescale (S.mε (E ω (ψ (θ n)))) (E ω (ψ (θ n)))
            (S.η ω) (u j ω (ψ (θ n)))) w atTop O := by
    apply Filter.Eventually.of_forall
    intro ω hP j O hO hOD ψ hψ
    obtain ⟨θ, hθ, hlim⟩ := hpath D hD E u C hEm hEr hE0 hum hCm ω hP.1 hP.2 ψ hψ
    obtain ⟨v, hv, hlocal⟩ := hlim j
    exact ⟨θ, hθ, v, hv.mono hOD, hlocal O hO hOD⟩
  obtain ⟨Φ, hΦm, hΦ⟩ := hS.exists_envSigma_local_rescale_of_relative_compactness
    (e ∘ φ) (fun n => he (φ n)) E hEm hEr u hum P D
    (fun j => (hD j).2.1) (fun j => (hD j).2.2.nonempty) hc
  refine ⟨Φ, hΦm, ?_⟩
  filter_upwards [hΦ] with ω hω
  exact ⟨hω.1, fun hA hb => hω.2 ⟨hA, hb⟩⟩

end MatedCRT
