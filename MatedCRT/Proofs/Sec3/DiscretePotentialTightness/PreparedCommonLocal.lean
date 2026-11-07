import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.CommonEventUniform
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.PathwiseRelativeCompactness

/-! # Prepared measurable local selection on a common event -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- The prepared pathwise step yields a single full-measure event on which
    every admissible family has a measurable locally convergent subsequence. -/
theorem preparedTightness_common_measurable_local (𝒮 : SpaceFillingSLEModel)
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
          ∀ ω ∈ A, PreparedTightnessBounds S D E u C ω → StrictMono (Φ ω) ∧
            ∀ j, ∃ v : ℂ → ℝ, ContinuousOn v (D j) ∧
              ∀ O, IsCompact O → O ⊆ D j → TendstoUniformlyOn
                (fun n => rescale (S.mε (E ω (Φ ω n))) (E ω (Φ ω n))
                  (S.η ω) (u j ω (Φ ω n))) v atTop O := by
  classical
  obtain ⟨φ, hφ, A, hA, hpath⟩ := preparedTightness_relative_compactness 𝒮 hp
    hγ hγ2 hρ hρ1 S hS e he he0
  obtain ⟨B, hB, huniform⟩ := hS.exists_commonEvent_uniform_rescale_randomMesh
  refine ⟨φ, hφ, A ∩ B, hA.and hB, ?_⟩
  intro D hD E u C hEm hEr hE0 hum hCm
  choose K x hK hx hd hcover hdom using fun j =>
    exists_compact_cover_dense_samples (D j) (hD j).2.1 (hD j).2.2.nonempty
  let P : Ω → ℕ → ℕ → Prop := fun ω _ _ => ω ∈ A ∧ PreparedTightnessBounds S D E u C ω
  have hc : ∀ ω ∈ B, ∀ j q, P ω j q → ∀ ψ : ℕ → ℕ, StrictMono ψ →
      ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ w : ℂ → ℝ, ContinuousOn w (K j q) ∧
        TendstoUniformlyOn (fun n => rescale (S.mε (E ω (ψ (θ n)))) (E ω (ψ (θ n)))
          (S.η ω) (u j ω (ψ (θ n)))) w atTop (K j q) := by
    intro ω _ j q hP ψ hψ
    obtain ⟨θ, hθ, hlim⟩ := hpath D hD E u C hEm hEr hE0 hum hCm ω hP.1 hP.2 ψ hψ
    obtain ⟨v, hv, hlocal⟩ := hlim j
    exact ⟨θ, hθ, v, hv.mono (hK j q).2, hlocal (K j q) (hK j q).1 (hK j q).2⟩
  obtain ⟨Φ, hΦm, hΦ⟩ := huniform (e ∘ φ) (fun n => he (φ n)) E hEm hEr u hum
    P K x hx hd hc
  refine ⟨Φ, hΦm, ?_⟩
  intro ω hω hb
  obtain ⟨hmono, hconv⟩ := hΦ ω hω.2
  refine ⟨hmono, ?_⟩
  intro j
  apply local_limit_of_uniform_compact_cover _ (D j) (K j) (hcover j) (hdom j)
  exact fun q => hconv j q ⟨hω.1, hb⟩

end MatedCRT
