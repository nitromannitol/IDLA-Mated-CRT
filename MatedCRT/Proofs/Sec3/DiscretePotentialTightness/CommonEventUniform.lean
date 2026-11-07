import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.CommonEventVertex
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.CompactCover

/-! # Uniform measurable selection on a common event -/

namespace MatedCRT

open Set MeasureTheory Filter Topology

/-- One common event supports measurable uniform selection on a countable
    family of compact sets, each with its own pathwise compactness condition. -/
theorem MatedCRTEnv.IsValid.exists_commonEvent_uniform_rescale_randomMesh
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∃ B : Set Ω, (∀ᵐ ω ∂S.P, ω ∈ B) ∧
      ∀ (e : ℕ → ℝ), (∀ j, 0 < e j) → ∀ (E : Ω → ℕ → ℝ),
      (∀ n, Measurable[S.envSigma] fun ω => E ω n) → (∀ ω n, E ω n ∈ range e) →
      ∀ (u : ℕ → Ω → ℕ → ℤ → ℝ),
      (∀ j n a, Measurable[S.envSigma] fun ω => u j ω n a) →
      ∀ (P : Ω → ℕ → ℕ → Prop) (K : ℕ → ℕ → Set ℂ) (x : ℕ → ℕ → ℕ → ℂ),
      (∀ j q i, x j q i ∈ K j q) → (∀ j q, K j q ⊆ closure (range (x j q))) →
      (∀ ω ∈ B, ∀ j q, P ω j q → ∀ ψ : ℕ → ℕ, StrictMono ψ →
        ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ w : ℂ → ℝ, ContinuousOn w (K j q) ∧
          TendstoUniformlyOn (fun n => rescale (S.mε (E ω (ψ (θ n)))) (E ω (ψ (θ n)))
            (S.η ω) (u j ω (ψ (θ n)))) w atTop (K j q)) →
      ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
        ∀ ω ∈ B, StrictMono (Φ ω) ∧ ∀ j q, P ω j q →
          ∃ w : ℂ → ℝ, ContinuousOn w (K j q) ∧
            TendstoUniformlyOn (fun n => rescale (S.mε (E ω (Φ ω n))) (E ω (Φ ω n))
              (S.η ω) (u j ω (Φ ω n))) w atTop (K j q) := by
  obtain ⟨B, hB, hdiag⟩ := hS.exists_commonEvent_diagonal_rescale_randomMesh
  refine ⟨B, hB, ?_⟩
  intro e he E hEm hEr u hu P K x hx hdense hc
  let samples : ℕ → ℂ := fun c => x c.unpair.1 c.unpair.2.unpair.1 c.unpair.2.unpair.2
  obtain ⟨Φ, hΦm, hΦ⟩ := hdiag e he E hEm hEr u hu samples
  refine ⟨Φ, hΦm, ?_⟩
  intro ω hω
  have hΦω := hΦ ω hω
  refine ⟨hΦω.1, ?_⟩
  intro j q hP
  have hcω := hc ω hω j q hP
  apply tendstoUniformlyOn_of_dense_subsequential_compactness (x j q) (hx j q) (hdense j q)
  · intro ψ hψ
    exact hcω (Φ ω ∘ ψ) (hΦω.1.comp hψ)
  · intro i
    have hb : ∃ M : ℝ, ∀ᶠ n in atTop,
        |rescale (S.mε (E ω n)) (E ω n) (S.η ω) (u j ω n) (x j q i)| ≤ M := by
      apply eventually_bounded_of_subsequential_compactness
      intro ψ hψ
      obtain ⟨θ, hθ, w, _, hw⟩ := hcω ψ hψ
      exact ⟨θ, hθ, w (x j q i), hw.tendsto_at (hx j q i)⟩
    have h := hΦω.2 j (Nat.pair j (Nat.pair q i)) (by simpa [samples] using hb)
    simpa [samples] using h

end MatedCRT
