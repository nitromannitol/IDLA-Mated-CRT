import Mathlib

/-!
# Gδ ranges of embeddings of Polish spaces

General topology used to identify Borel probability measures on a Polish space with probability
measures on a compact metrizable space that are carried by a Gδ set.

* `MatedCRT.isGδ_range_of_isEmbedding`: the range of a topological embedding of a Polish space into a
  metrizable space is a Gδ set.
* `MatedCRT.polishSpace_subtype_of_isGδ`: a Gδ subset of a Polish space is Polish.
* `MatedCRT.exists_isEmbedding_hilbertCube_isGδ`: a Polish space embeds into the Hilbert cube
  `ℕ → unitInterval` with Gδ range.
-/

namespace MatedCRT

open Set Filter Topology

/-- In a complete metric space `X`, the range of a topological embedding `i : X → Z` into a
metrizable space is a Gδ set. It is the intersection of its closure with the open sets `U n`, the
union of the open sets `V` whose preimage `i ⁻¹' V` has all distances `< 1 / (n + 1)`. -/
theorem isGδ_range_of_isEmbedding_of_completeSpace {X Z : Type*} [MetricSpace X] [CompleteSpace X]
    [TopologicalSpace Z] [TopologicalSpace.MetrizableSpace Z] {i : X → Z} (hi : IsEmbedding i) :
    IsGδ (range i) := by
  set U : ℕ → Set Z := fun n => ⋃₀ {V | IsOpen V ∧
    ∀ x ∈ i ⁻¹' V, ∀ y ∈ i ⁻¹' V, dist x y < 1 / ((n : ℝ) + 1)}
  have hUo : ∀ n, IsOpen (U n) := fun n => isOpen_sUnion fun V hV => hV.1
  have key : range i = closure (range i) ∩ ⋂ n, U n := by
    apply Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      refine ⟨subset_closure (mem_range_self x), mem_iInter.2 fun n => ?_⟩
      have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) / 2 := by positivity
      have hball : Metric.ball x (1 / ((n : ℝ) + 1) / 2) ∈ comap i (𝓝 (i x)) := by
        rw [← hi.isInducing.nhds_eq_comap]
        exact Metric.ball_mem_nhds x hε
      obtain ⟨t, ht, hts⟩ := mem_comap.1 hball
      obtain ⟨V, hVt, hVo, hxV⟩ := mem_nhds_iff.1 ht
      refine mem_sUnion.2 ⟨V, ⟨hVo, fun y hy y' hy' => ?_⟩, hxV⟩
      have h1 : dist y x < 1 / ((n : ℝ) + 1) / 2 := hts (hVt hy)
      have h2 : dist y' x < 1 / ((n : ℝ) + 1) / 2 := hts (hVt hy')
      calc dist y y' ≤ dist y x + dist y' x := dist_triangle_right y y' x
        _ < 1 / ((n : ℝ) + 1) / 2 + 1 / ((n : ℝ) + 1) / 2 := add_lt_add h1 h2
        _ = 1 / ((n : ℝ) + 1) := add_halves _
    · rintro z ⟨hzcl, hzU⟩
      have hne : (comap i (𝓝 z)).NeBot := by
        rw [comap_neBot_iff]
        intro t ht
        obtain ⟨_, hzt, a, rfl⟩ := mem_closure_iff_nhds.1 hzcl t ht
        exact ⟨a, hzt⟩
      have hcau : Cauchy (comap i (𝓝 z)) := by
        refine Metric.cauchy_iff.2 ⟨hne, fun ε hε => ?_⟩
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
        obtain ⟨V, ⟨hVo, hV⟩, hzV⟩ := mem_sUnion.1 (mem_iInter.1 hzU n)
        exact ⟨i ⁻¹' V, preimage_mem_comap (hVo.mem_nhds hzV),
          fun x hx y hy => (hV x hx y hy).trans hn⟩
      obtain ⟨x, hx⟩ := CompleteSpace.complete hcau
      have h1 : Tendsto i (comap i (𝓝 z)) (𝓝 z) := tendsto_comap
      have h2 : Tendsto i (comap i (𝓝 z)) (𝓝 (i x)) := (hi.continuous.tendsto x).mono_left hx
      exact ⟨x, (tendsto_nhds_unique h1 h2).symm⟩
  rw [key]
  exact isClosed_closure.isGδ.inter (IsGδ.iInter_of_isOpen hUo)

/-- The range of a topological embedding of a Polish space into a metrizable space is a Gδ set. -/
theorem isGδ_range_of_isEmbedding {X Z : Type*} [TopologicalSpace X] [PolishSpace X]
    [TopologicalSpace Z] [TopologicalSpace.MetrizableSpace Z] {i : X → Z}
    (hi : Topology.IsEmbedding i) : IsGδ (Set.range i) := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable X
  exact isGδ_range_of_isEmbedding_of_completeSpace hi

/-- A Gδ subset of a Polish space is Polish: writing `G = ⋂ n, U n` with `U n` open, the map
`G → Π n, U n`, `z ↦ (z, z, …)`, is a closed embedding into a countable product of Polish spaces. -/
theorem polishSpace_subtype_of_isGδ {Z : Type*} [TopologicalSpace Z] [PolishSpace Z] {G : Set Z}
    (hG : IsGδ G) : PolishSpace G := by
  obtain ⟨U, hUo, rfl⟩ := isGδ_iff_eq_iInter_nat.1 hG
  have : ∀ n, PolishSpace (U n) := fun n => (hUo n).polishSpace
  let J : (⋂ n, U n : Set Z) → ((n : ℕ) → U n) := fun z n => ⟨z.1, mem_iInter.1 z.2 n⟩
  have hJc : Continuous J := continuous_pi fun n => Continuous.subtype_mk continuous_subtype_val _
  have hev : ∀ n, Continuous fun f : (n : ℕ) → U n => ((f n : U n) : Z) := fun n =>
    continuous_subtype_val.comp (continuous_apply n)
  have hJ : IsClosedEmbedding J := by
    refine ⟨⟨IsInducing.of_comp hJc (hev 0) IsEmbedding.subtypeVal.isInducing, fun a b hab => ?_⟩, ?_⟩
    · exact Subtype.ext (congrArg (fun f : (n : ℕ) → U n => ((f 0 : U 0) : Z)) hab)
    · have hrange : range J = {f | ∀ n, ((f n : U n) : Z) = ((f 0 : U 0) : Z)} := by
        ext f
        constructor
        · rintro ⟨z, rfl⟩ n
          rfl
        · intro hf
          refine ⟨⟨((f 0 : U 0) : Z), mem_iInter.2 fun n => ?_⟩, funext fun n => Subtype.ext (hf n).symm⟩
          rw [← hf n]
          exact (f n).2
      rw [hrange, ofPred_forall]
      exact isClosed_iInter fun n => isClosed_eq (hev n) (hev 0)
  exact hJ.polishSpace

/-- A Polish space embeds into the Hilbert cube `ℕ → unitInterval`, and the range of the embedding
is a Gδ set. -/
theorem exists_isEmbedding_hilbertCube_isGδ (X : Type*) [TopologicalSpace X] [PolishSpace X] :
    ∃ i : X → (ℕ → unitInterval), Topology.IsEmbedding i ∧ IsGδ (Set.range i) := by
  obtain ⟨i, hi⟩ : ∃ i : X → (ℕ → unitInterval), Topology.IsEmbedding i := by
    let := TopologicalSpace.upgradeIsCompletelyMetrizable X
    exact Metric.PiNatEmbed.exists_embedding_to_hilbert_cube
  exact ⟨i, hi, isGδ_range_of_isEmbedding hi⟩

end MatedCRT
