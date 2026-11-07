import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.RandomMeshConditional

/-! # Compact covers and dense samples for open domains -/

namespace MatedCRT

open Set Topology MeasureTheory Filter

/-- A nonempty open planar domain has a countable compact cover with dense
samples in each member, cofinal among compact subsets of the domain. -/
theorem exists_compact_cover_dense_samples (D : Set ℂ) (hD : IsOpen D)
    (hne : D.Nonempty) :
    ∃ (K : ℕ → Set ℂ) (x : ℕ → ℕ → ℂ),
      (∀ q, IsCompact (K q) ∧ K q ⊆ D) ∧
      (∀ q i, x q i ∈ K q) ∧
      (∀ q, K q ⊆ closure (range (x q))) ∧
      (∀ z ∈ D, ∃ q, z ∈ interior (K q)) ∧
      (∀ O, IsCompact O → O ⊆ D → ∃ q, O ⊆ K q) := by
  classical
  let : LocallyCompactSpace D := hD.locallyCompactSpace
  let L : CompactExhaustion D := CompactExhaustion.choice D
  obtain ⟨z₀, hz₀⟩ := hne
  let K : ℕ → Set ℂ := fun q => Subtype.val '' L q ∪ {z₀}
  have hcompact : ∀ q, IsCompact (K q) := fun q =>
    ((L.isCompact q).image continuous_subtype_val).union isCompact_singleton
  have hsub : ∀ q, K q ⊆ D := by
    intro q z hz
    rcases hz with ⟨y, hy, rfl⟩ | hz
    · exact y.property
    · simpa only [mem_singleton_iff] using hz ▸ hz₀
  have hneK : ∀ q, (K q).Nonempty := fun q => ⟨z₀, Or.inr rfl⟩
  have hdense : ∀ q, ∃ x : ℕ → ℂ, (∀ i, x i ∈ K q) ∧ K q ⊆ closure (range x) := by
    intro q
    let : Nonempty (K q) := ⟨⟨z₀, Or.inr rfl⟩⟩
    obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (K q)
    refine ⟨fun i => (u i).val, fun i => (u i).property, ?_⟩
    intro z hz
    have hh := hu ⟨z, hz⟩
    simpa only [range_comp'] using (closure_subtype.1 hh)
  choose x hx hd using hdense
  refine ⟨K, x, fun q => ⟨hcompact q, hsub q⟩, hx, hd, ?_, ?_⟩
  · intro z hz
    obtain ⟨q, hq⟩ := L.exists_mem ⟨z, hz⟩
    refine ⟨q + 1, ?_⟩
    apply interior_mono (show Subtype.val '' L (q + 1) ⊆ K (q + 1) from subset_union_left)
    apply hD.isOpenEmbedding_subtypeVal.isOpenMap.image_interior_subset
    exact ⟨⟨z, hz⟩, L.subset_interior_succ q hq, rfl⟩
  · intro O hO hOD
    have hpre : IsCompact (Subtype.val ⁻¹' O : Set D) := by
      rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, image_preimage_eq_inter_range]
      simpa [Subtype.range_coe, inter_eq_left.mpr hOD] using hO
    obtain ⟨q, hq⟩ := L.exists_superset_of_isCompact hpre
    refine ⟨q, ?_⟩
    intro z hz
    exact Or.inl ⟨⟨z, hOD hz⟩, hq hz, rfl⟩

/-- Countably many open domains admit a common measurable random-mesh
    subsequence whenever the fields are relatively compact locally on a good event. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_local_rescale_of_relative_compactness
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (e : ℕ → ℝ) (he : ∀ j, 0 < e j) (E : Ω → ℕ → ℝ)
    (hEm : ∀ n, Measurable[S.envSigma] fun ω => E ω n)
    (hEr : ∀ ω n, E ω n ∈ range e)
    (u : ℕ → Ω → ℕ → ℤ → ℝ)
    (hu : ∀ j n a, Measurable[S.envSigma] fun ω => u j ω n a)
    (P : Ω → Prop) (D : ℕ → Set ℂ)
    (hDo : ∀ j, IsOpen (D j)) (hDn : ∀ j, (D j).Nonempty)
    (hc : ∀ᵐ ω ∂S.P, P ω → ∀ j O, IsCompact O → O ⊆ D j →
      ∀ (ψ : ℕ → ℕ), StrictMono ψ →
      ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ w : ℂ → ℝ, ContinuousOn w O ∧
        TendstoUniformlyOn (fun n => rescale (S.mε (E ω (ψ (θ n)))) (E ω (ψ (θ n)))
          (S.η ω) (u j ω (ψ (θ n)))) w atTop O) :
    ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
      ∀ᵐ ω ∂S.P, StrictMono (Φ ω) ∧ (P ω → ∀ j, ∃ v : ℂ → ℝ,
        ContinuousOn v (D j) ∧ ∀ O, IsCompact O → O ⊆ D j → TendstoUniformlyOn
          (fun n => rescale (S.mε (E ω (Φ ω n))) (E ω (Φ ω n))
            (S.η ω) (u j ω (Φ ω n))) v atTop O) := by
  classical
  choose K x hK hx hd hcover hdom using fun j =>
    exists_compact_cover_dense_samples (D j) (hDo j) (hDn j)
  apply hS.exists_envSigma_local_rescale_randomMesh_on_event e he E hEm hEr u hu
    P D K x hx hd hcover hdom
  filter_upwards [hc] with ω hω hP j q ψ hψ
  exact hω hP j (K j q) (hK j q).1 (hK j q).2 ψ hψ

end MatedCRT
