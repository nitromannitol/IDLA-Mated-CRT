import MatedCRT.Draft.Section3Prepared

/-! Single-domain extraction from the deterministic preparation in Lemma 3.1. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- After deterministic preparation, measurable data satisfying the hypotheses
almost surely admit an environment-measurable convergent subsequence. -/
theorem preparedTightness_singleDomain (𝒮 : SpaceFillingSLEModel)
    (h31 : DiscretePotentialTightnessPreparedStmt 𝒮) {γ ρ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∀ (D : Set ℂ), D ⊆ ball 0 ρ → IsOpen D → IsConnected D →
    ∀ (E : Ω → ℕ → ℝ) (u : Ω → ℕ → ℤ → ℝ) (C : Ω → ℝ),
      (∀ n, Measurable[S.envSigma] fun ω => E ω n) →
      (∀ ω n, E ω n ∈ range (e ∘ φ)) → (∀ ω, Tendsto (E ω) atTop (𝓝 0)) →
      (∀ n a, Measurable[S.envSigma] fun ω => u ω n a) → Measurable[S.envSigma] C →
      (∀ᵐ ω ∂S.P, 0 < C ω ∧
        (∀ n, ∀ a ∈ interiorCellVertices (E ω n) (S.η ω) D,
          |matedLaplacian (S.mult (E ω n) ω) (u ω n) a| ≤ C ω) ∧
        (∀ n, ∀ a ∈ cellVertices (E ω n) (S.η ω) D, |u ω n a| ≤ C ω / E ω n)) →
      ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
        ∀ᵐ ω ∂S.P, StrictMono (Φ ω) ∧ PreparedTightnessLimit S D E u Φ ω := by
  obtain ⟨φ, hφ, A, hA, hprep⟩ := h31 γ hγ hγ2 ρ hρ hρ1 Ω S hS e he he0
  refine ⟨φ, hφ, ?_⟩
  intro D hD hDo hDc E u C hEm hEr hE0 hum hCm hbound
  obtain ⟨Φ, hΦm, hΦ⟩ := hprep (fun _ => D) (fun _ => ⟨hD, hDo, hDc⟩)
    E (fun _ => u) (fun _ => C) hEm hEr hE0 (fun _ => hum) (fun _ => hCm)
  refine ⟨Φ, hΦm, ?_⟩
  filter_upwards [hA, hbound] with ω hω hb
  have hbounds : PreparedTightnessBounds S (fun _ => D) E (fun _ => u) (fun _ => C) ω :=
    fun _ => hb
  obtain ⟨hm, hl⟩ := hΦ ω hω hbounds
  exact ⟨hm, hl 0⟩

end MatedCRT
