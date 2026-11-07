import MatedCRT.Steps.Sec3.DiscretePotentialTightnessPrepared

/-! # Prepared pathwise compactness with boundary convergence -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- The prepared pathwise conclusion remains valid after reindexing, including
    uniform convergence on the closure under the original boundary hypothesis. -/
theorem preparedTightness_boundary_relative_compactness (𝒮 : SpaceFillingSLEModel)
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
        ∀ ω ∈ A, PreparedTightnessBounds S D E u C ω →
        ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ θ : ℕ → ℕ, StrictMono θ ∧
          ∀ j, ∃ v : ℂ → ℝ, ContinuousOn v (D j) ∧
            (∀ O, IsCompact O → O ⊆ D j → TendstoUniformlyOn
              (fun n => rescale (S.mε (E ω (ψ (θ n)))) (E ω (ψ (θ n)))
                (S.η ω) (u j ω (ψ (θ n)))) v atTop O) ∧
            (PreparedHolderBoundary S (D j) E (u j) ω → TendstoUniformlyOn
              (fun n => rescale (S.mε (E ω (ψ (θ n)))) (E ω (ψ (θ n)))
                (S.η ω) (u j ω (ψ (θ n)))) v atTop (closure (D j))) := by
  obtain ⟨φ, hφ, A, hA, hpath⟩ := hp γ hγ hγ2 ρ hρ hρ1 Ω S hS e he he0
  refine ⟨φ, hφ, A, hA, ?_⟩
  intro D hD E u C hEm hEr hE0 hum hCm ω hω hb ψ hψ
  let E' : Ω → ℕ → ℝ := fun ω n => E ω (ψ n)
  let u' : ℕ → Ω → ℕ → ℤ → ℝ := fun j ω n => u j ω (ψ n)
  have hb' : PreparedTightnessBounds S D E' u' C ω := by
    intro j
    exact ⟨(hb j).1, fun n => (hb j).2.1 (ψ n), fun n => (hb j).2.2 (ψ n)⟩
  obtain ⟨θ, hθ, hlim⟩ := hpath D hD E' u' C (fun n => hEm (ψ n))
    (fun ω n => hEr ω (ψ n)) (fun ω => (hE0 ω).comp hψ.tendsto_atTop)
    (fun j n a => hum j (ψ n) a) hCm ω hω hb'
  refine ⟨θ, hθ, ?_⟩
  intro j
  obtain ⟨v, hv, hlocal, hboundary⟩ := hlim j
  refine ⟨v, hv, ?_, ?_⟩
  · intro O hO hOD
    exact hlocal O hO (by rwa [hO.isClosed.closure_eq])
  · intro hholder
    apply hboundary
    obtain ⟨hsimple, hharm, χ, C', hχ, hχ1, hC, hmod⟩ := hholder
    exact ⟨hsimple, fun n => hharm (ψ n), χ, C', hχ, hχ1, hC,
      fun n => hmod (ψ n)⟩

end MatedCRT
