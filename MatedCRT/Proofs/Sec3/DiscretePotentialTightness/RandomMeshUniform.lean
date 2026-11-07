import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.RandomMeshVertex
import MatedCRT.Proofs.Sec4.SubsequentialConvergence.PreparedPointBounds

/-! # Measurable uniform subsequences on countable compact sets -/

namespace MatedCRT

open Set MeasureTheory Filter Topology

/-- Relative compactness on countably many compact sets upgrades the measurable
    diagonal of sampled random-mesh fields to uniform convergence on each set. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_uniform_rescale_randomMesh
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (e : ℕ → ℝ) (he : ∀ j, 0 < e j) (E : Ω → ℕ → ℝ)
    (hEm : ∀ n, Measurable[S.envSigma] fun ω => E ω n)
    (hEr : ∀ ω n, E ω n ∈ range e)
    (u : ℕ → Ω → ℕ → ℤ → ℝ)
    (hu : ∀ j n a, Measurable[S.envSigma] fun ω => u j ω n a)
    (K : ℕ → ℕ → Set ℂ) (x : ℕ → ℕ → ℕ → ℂ)
    (hx : ∀ j q i, x j q i ∈ K j q) (hdense : ∀ j q, K j q ⊆ closure (range (x j q)))
    (hc : ∀ᵐ ω ∂S.P, ∀ j q (ψ : ℕ → ℕ), StrictMono ψ →
      ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ w : ℂ → ℝ, ContinuousOn w (K j q) ∧
        TendstoUniformlyOn (fun n => rescale (S.mε (E ω (ψ (θ n)))) (E ω (ψ (θ n)))
          (S.η ω) (u j ω (ψ (θ n)))) w atTop (K j q)) :
    ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
      ∀ᵐ ω ∂S.P, StrictMono (Φ ω) ∧ ∀ j q, ∃ w : ℂ → ℝ, ContinuousOn w (K j q) ∧
        TendstoUniformlyOn (fun n => rescale (S.mε (E ω (Φ ω n))) (E ω (Φ ω n))
          (S.η ω) (u j ω (Φ ω n))) w atTop (K j q) := by
  let samples : ℕ → ℂ := fun c => x c.unpair.1 c.unpair.2.unpair.1 c.unpair.2.unpair.2
  obtain ⟨Φ, hΦm, hΦ⟩ := hS.exists_envSigma_diagonal_rescale_randomMesh e he E hEm hEr u hu samples
  refine ⟨Φ, hΦm, ?_⟩
  filter_upwards [hΦ, hc] with ω hΦω hcω
  refine ⟨hΦω.1, ?_⟩
  intro j q
  apply tendstoUniformlyOn_of_dense_subsequential_compactness (x j q) (hx j q) (hdense j q)
  · intro ψ hψ
    exact hcω j q (Φ ω ∘ ψ) (hΦω.1.comp hψ)
  · intro i
    have hb : ∃ M : ℝ, ∀ᶠ n in atTop,
        |rescale (S.mε (E ω n)) (E ω n) (S.η ω) (u j ω n) (x j q i)| ≤ M := by
      apply eventually_bounded_of_subsequential_compactness
      intro ψ hψ
      obtain ⟨θ, hθ, w, _, hw⟩ := hcω j q ψ hψ
      exact ⟨θ, hθ, w (x j q i), hw.tendsto_at (hx j q i)⟩
    have h := hΦω.2 j (Nat.pair j (Nat.pair q i)) (by simpa [samples] using hb)
    simpa [samples] using h

/-- Uniform limits on a compact cover with interior neighborhoods agree on
    overlaps and define one continuous local limit. -/
theorem local_limit_of_uniform_compact_cover
    (F : ℕ → ℂ → ℝ) (D : Set ℂ) (K : ℕ → Set ℂ)
    (hcover : ∀ x ∈ D, ∃ q, x ∈ interior (K q))
    (hdom : ∀ O : Set ℂ, IsCompact O → O ⊆ D → ∃ q, O ⊆ K q)
    (hconv : ∀ q, ∃ w : ℂ → ℝ, ContinuousOn w (K q) ∧
      TendstoUniformlyOn F w atTop (K q)) :
    ∃ v : ℂ → ℝ, ContinuousOn v D ∧
      ∀ O : Set ℂ, IsCompact O → O ⊆ D → TendstoUniformlyOn F v atTop O := by
  choose w hwc hw using hconv
  let v : ℂ → ℝ := fun x => limUnder atTop (fun n => F n x)
  have heq : ∀ q, EqOn (w q) v (K q) := by
    intro q x hx
    exact (hw q).tendsto_at hx |>.limUnder_eq.symm
  refine ⟨v, ?_, ?_⟩
  · apply continuousOn_of_locally_continuousOn
    intro x hx
    obtain ⟨q, hq⟩ := hcover x hx
    refine ⟨interior (K q), isOpen_interior, hq, ?_⟩
    exact ((hwc q).mono (fun _ hy => interior_subset hy.2)).congr
      (fun y hy => (heq q (interior_subset hy.2)).symm)
  · intro O hO hOD
    obtain ⟨q, hq⟩ := hdom O hO hOD
    exact ((hw q).congr_right (heq q)).mono hq

/-- A measurable subsequence converges locally on every domain of a countable
    family, given relative compactness on countable compact covers. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_local_rescale_randomMesh
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (e : ℕ → ℝ) (he : ∀ j, 0 < e j) (E : Ω → ℕ → ℝ)
    (hEm : ∀ n, Measurable[S.envSigma] fun ω => E ω n)
    (hEr : ∀ ω n, E ω n ∈ range e)
    (u : ℕ → Ω → ℕ → ℤ → ℝ)
    (hu : ∀ j n a, Measurable[S.envSigma] fun ω => u j ω n a)
    (D : ℕ → Set ℂ) (K : ℕ → ℕ → Set ℂ) (x : ℕ → ℕ → ℕ → ℂ)
    (hx : ∀ j q i, x j q i ∈ K j q) (hdense : ∀ j q, K j q ⊆ closure (range (x j q)))
    (hcover : ∀ j z, z ∈ D j → ∃ q, z ∈ interior (K j q))
    (hdom : ∀ j O, IsCompact O → O ⊆ D j → ∃ q, O ⊆ K j q)
    (hc : ∀ᵐ ω ∂S.P, ∀ j q (ψ : ℕ → ℕ), StrictMono ψ →
      ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ w : ℂ → ℝ, ContinuousOn w (K j q) ∧
        TendstoUniformlyOn (fun n => rescale (S.mε (E ω (ψ (θ n)))) (E ω (ψ (θ n)))
          (S.η ω) (u j ω (ψ (θ n)))) w atTop (K j q)) :
    ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
      ∀ᵐ ω ∂S.P, StrictMono (Φ ω) ∧ ∀ j, ∃ v : ℂ → ℝ, ContinuousOn v (D j) ∧
        ∀ O, IsCompact O → O ⊆ D j → TendstoUniformlyOn
          (fun n => rescale (S.mε (E ω (Φ ω n))) (E ω (Φ ω n))
            (S.η ω) (u j ω (Φ ω n))) v atTop O := by
  obtain ⟨Φ, hΦm, hΦ⟩ := hS.exists_envSigma_uniform_rescale_randomMesh e he E hEm hEr u hu
    K x hx hdense hc
  refine ⟨Φ, hΦm, ?_⟩
  filter_upwards [hΦ] with ω hω
  refine ⟨hω.1, fun j => ?_⟩
  exact local_limit_of_uniform_compact_cover _ (D j) (K j) (hcover j) (hdom j) (hω.2 j)

end MatedCRT
