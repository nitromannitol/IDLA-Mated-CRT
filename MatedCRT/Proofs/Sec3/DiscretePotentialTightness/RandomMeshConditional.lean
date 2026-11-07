import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.RandomMeshUniform

/-! # Conditional measurable uniform subsequences -/

namespace MatedCRT

open Set MeasureTheory Filter Topology

/-- Measurable uniform selection on an arbitrary good event. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_uniform_rescale_randomMesh_on_event
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (e : ℕ → ℝ) (he : ∀ j, 0 < e j) (E : Ω → ℕ → ℝ)
    (hEm : ∀ n, Measurable[S.envSigma] fun ω => E ω n)
    (hEr : ∀ ω n, E ω n ∈ range e)
    (u : ℕ → Ω → ℕ → ℤ → ℝ)
    (hu : ∀ j n a, Measurable[S.envSigma] fun ω => u j ω n a)
    (P : Ω → Prop)
    (K : ℕ → ℕ → Set ℂ) (x : ℕ → ℕ → ℕ → ℂ)
    (hx : ∀ j q i, x j q i ∈ K j q) (hdense : ∀ j q, K j q ⊆ closure (range (x j q)))
    (hc : ∀ᵐ ω ∂S.P, P ω → ∀ j q (ψ : ℕ → ℕ), StrictMono ψ →
      ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ w : ℂ → ℝ, ContinuousOn w (K j q) ∧
        TendstoUniformlyOn (fun n => rescale (S.mε (E ω (ψ (θ n)))) (E ω (ψ (θ n)))
          (S.η ω) (u j ω (ψ (θ n)))) w atTop (K j q)) :
    ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
      ∀ᵐ ω ∂S.P, StrictMono (Φ ω) ∧ (P ω → ∀ j q, ∃ w : ℂ → ℝ, ContinuousOn w (K j q) ∧
        TendstoUniformlyOn (fun n => rescale (S.mε (E ω (Φ ω n))) (E ω (Φ ω n))
          (S.η ω) (u j ω (Φ ω n))) w atTop (K j q)) := by
  let samples : ℕ → ℂ := fun c => x c.unpair.1 c.unpair.2.unpair.1 c.unpair.2.unpair.2
  obtain ⟨Φ, hΦm, hΦ⟩ := hS.exists_envSigma_diagonal_rescale_randomMesh e he E hEm hEr u hu samples
  refine ⟨Φ, hΦm, ?_⟩
  filter_upwards [hΦ, hc] with ω hΦω hcω
  refine ⟨hΦω.1, ?_⟩
  intro hP j q
  have hcω := hcω hP
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


/-- Measurable local selection on an arbitrary good event. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_local_rescale_randomMesh_on_event
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (e : ℕ → ℝ) (he : ∀ j, 0 < e j) (E : Ω → ℕ → ℝ)
    (hEm : ∀ n, Measurable[S.envSigma] fun ω => E ω n)
    (hEr : ∀ ω n, E ω n ∈ range e)
    (u : ℕ → Ω → ℕ → ℤ → ℝ)
    (hu : ∀ j n a, Measurable[S.envSigma] fun ω => u j ω n a)
    (P : Ω → Prop)
    (D : ℕ → Set ℂ) (K : ℕ → ℕ → Set ℂ) (x : ℕ → ℕ → ℕ → ℂ)
    (hx : ∀ j q i, x j q i ∈ K j q) (hdense : ∀ j q, K j q ⊆ closure (range (x j q)))
    (hcover : ∀ j z, z ∈ D j → ∃ q, z ∈ interior (K j q))
    (hdom : ∀ j O, IsCompact O → O ⊆ D j → ∃ q, O ⊆ K j q)
    (hc : ∀ᵐ ω ∂S.P, P ω → ∀ j q (ψ : ℕ → ℕ), StrictMono ψ →
      ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ w : ℂ → ℝ, ContinuousOn w (K j q) ∧
        TendstoUniformlyOn (fun n => rescale (S.mε (E ω (ψ (θ n)))) (E ω (ψ (θ n)))
          (S.η ω) (u j ω (ψ (θ n)))) w atTop (K j q)) :
    ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
      ∀ᵐ ω ∂S.P, StrictMono (Φ ω) ∧ (P ω → ∀ j, ∃ v : ℂ → ℝ, ContinuousOn v (D j) ∧
        ∀ O, IsCompact O → O ⊆ D j → TendstoUniformlyOn
          (fun n => rescale (S.mε (E ω (Φ ω n))) (E ω (Φ ω n))
            (S.η ω) (u j ω (Φ ω n))) v atTop O) := by
  obtain ⟨Φ, hΦm, hΦ⟩ := hS.exists_envSigma_uniform_rescale_randomMesh_on_event e he E hEm hEr u hu
    P K x hx hdense hc
  refine ⟨Φ, hΦm, ?_⟩
  filter_upwards [hΦ] with ω hω
  refine ⟨hω.1, fun hP j => ?_⟩
  exact local_limit_of_uniform_compact_cover _ (D j) (K j) (hcover j) (hdom j) (hω.2 hP j)

/-- A single measurable selection works for compact sets with separate good events. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_uniform_rescale_randomMesh_on_events
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (e : ℕ → ℝ) (he : ∀ j, 0 < e j) (E : Ω → ℕ → ℝ)
    (hEm : ∀ n, Measurable[S.envSigma] fun ω => E ω n)
    (hEr : ∀ ω n, E ω n ∈ range e)
    (u : ℕ → Ω → ℕ → ℤ → ℝ)
    (hu : ∀ j n a, Measurable[S.envSigma] fun ω => u j ω n a)
    (P : Ω → ℕ → ℕ → Prop)
    (K : ℕ → ℕ → Set ℂ) (x : ℕ → ℕ → ℕ → ℂ)
    (hx : ∀ j q i, x j q i ∈ K j q) (hdense : ∀ j q, K j q ⊆ closure (range (x j q)))
    (hc : ∀ᵐ ω ∂S.P, ∀ j q, P ω j q → ∀ (ψ : ℕ → ℕ), StrictMono ψ →
      ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ w : ℂ → ℝ, ContinuousOn w (K j q) ∧
        TendstoUniformlyOn (fun n => rescale (S.mε (E ω (ψ (θ n)))) (E ω (ψ (θ n)))
          (S.η ω) (u j ω (ψ (θ n)))) w atTop (K j q)) :
    ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
      ∀ᵐ ω ∂S.P, StrictMono (Φ ω) ∧ (∀ j q, P ω j q → ∃ w : ℂ → ℝ, ContinuousOn w (K j q) ∧
        TendstoUniformlyOn (fun n => rescale (S.mε (E ω (Φ ω n))) (E ω (Φ ω n))
          (S.η ω) (u j ω (Φ ω n))) w atTop (K j q)) := by
  let samples : ℕ → ℂ := fun c => x c.unpair.1 c.unpair.2.unpair.1 c.unpair.2.unpair.2
  obtain ⟨Φ, hΦm, hΦ⟩ := hS.exists_envSigma_diagonal_rescale_randomMesh e he E hEm hEr u hu samples
  refine ⟨Φ, hΦm, ?_⟩
  filter_upwards [hΦ, hc] with ω hΦω hcω
  refine ⟨hΦω.1, ?_⟩
  intro j q hP
  have hcω := hcω j q hP
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
