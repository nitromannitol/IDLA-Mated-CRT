import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.DyadicModulus

/-! Probability estimates from deterministic preparation and pathwise compactness. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- Deterministic preparation followed by pathwise compactness along every
subsequence forces diagonal oscillation probabilities to vanish. -/
theorem tendsto_oscillation_probability_of_prepared_compactness
    {Ω α : Type*} [MeasurableSpace Ω] [PseudoMetricSpace α]
    (P : Measure Ω) [IsFiniteMeasure P] (K : Set α) (hK : IsCompact K)
    (F : ℕ → Ω → α → ℝ) (t : ℝ) (ht : 0 < t)
    (hA : ∀ n : ℕ, NullMeasurableSet {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < 1 / ((n : ℝ) + 1) ∧ t < |F n ω x - F n ω y|} P)
    (hcompact : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ ω ∂P, ∀ θ : ℕ → ℕ, StrictMono θ → ∃ η : ℕ → ℕ, StrictMono η ∧
        ∃ u : α → ℝ, ContinuousOn u K ∧ TendstoUniformlyOn
          (fun k => F (ψ (φ (θ (η k)))) ω) u atTop K) :
    Tendsto (fun n : ℕ => P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < 1 / ((n : ℝ) + 1) ∧ t < |F n ω x - F n ω y|}) atTop (𝓝 0) := by
  classical
  let A : ℕ → Set Ω := fun n => {ω | ∃ x ∈ K, ∃ y ∈ K,
    dist x y < 1 / ((n : ℝ) + 1) ∧ t < |F n ω x - F n ω y|}
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨σ, hσ, hnsσ⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨φ, hφ, hcompactφ⟩ := hcompact (ns ∘ σ) hnsσ
  refine ⟨σ ∘ φ, ?_⟩
  apply tendsto_measure_zero_of_ae_eventually_not_mem P (fun n => A (ns (σ (φ n))))
    (fun n => hA _)
  filter_upwards [hcompactφ] with ω hω
  by_contra hnot
  have hfrequent : ∀ n, ∃ j, n ≤ j ∧ ω ∈ A (ns (σ (φ j))) := by
    intro n
    by_contra hnone
    apply hnot
    filter_upwards [eventually_ge_atTop n] with j hj
    exact fun hm => hnone ⟨j, hj, hm⟩
  choose g hg using hfrequent
  obtain ⟨τ, hτ, hgτ⟩ := strictMono_subseq_of_id_le (fun n => (hg n).1)
  obtain ⟨η, hη, u, hu, hconv⟩ := hω (g ∘ τ) hgτ
  have hevent := eventually_small_oscillation_of_uniform_subsequence K hK
    (fun n => F (ns (σ (φ (g (τ n))))) ω) u η hη hu hconv ht
  obtain ⟨k, hk⟩ := hevent.exists
  obtain ⟨x, hx, y, hy, hxy, hbad⟩ := (hg (τ (η k))).2
  have hden : (0 : ℝ) < (η k : ℝ) + 1 := by positivity
  have hge : η k ≤ ns (σ (φ (g (τ (η k))))) :=
    (hgτ.id_le (η k)).trans (hφ.id_le _ |>.trans (hnsσ.id_le _))
  have hscale : 1 / ((ns (σ (φ (g (τ (η k))))) : ℝ) + 1) ≤
      1 / ((η k : ℝ) + 1) := by
    apply one_div_le_one_div_of_le hden
    exact_mod_cast Nat.add_le_add_right hge 1
  exact (not_lt_of_ge (hk x hx y hy (hxy.trans_le hscale)).le) hbad

/-- Prepared compactness along dyadic mesh sequences gives a spatial modulus
in probability for the full one-sided mesh limit. -/
theorem mesh_modulus_of_dyadic_prepared_compactness
    {Ω α : Type*} [MeasurableSpace Ω] [PseudoMetricSpace α]
    (P : Measure Ω) [IsFiniteMeasure P] (K : Set α) (hK : IsCompact K)
    (F : ℝ → Ω → α → ℝ) (t : ℝ) (ht : 0 < t)
    (hA : ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ,
      NullMeasurableSet {ω | ∃ x ∈ K, ∃ y ∈ K,
        dist x y < δ ∧ t < |F ε ω x - F ε ω y|} P)
    (hcompact : ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n ∧ ε n < (1 / 2) ^ n) →
      ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ᵐ ω ∂P, ∀ θ : ℕ → ℕ, StrictMono θ → ∃ η : ℕ → ℕ, StrictMono η ∧
          ∃ u : α → ℝ, ContinuousOn u K ∧ TendstoUniformlyOn
            (fun k => F (ε (ψ (φ (θ (η k))))) ω) u atTop K)
    {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < δ ∧ t < |F ε ω x - F ε ω y|} ≤ e := by
  let E : ℝ → ℝ → Set Ω := fun δ ε => {ω | ∃ x ∈ K, ∃ y ∈ K,
    dist x y < δ ∧ t < |F ε ω x - F ε ω y|}
  refine @asymptotic_modulus_of_dyadic_mesh_sequences Ω _ P E ?_ ?_ e he
  · intro δ δ' ε hδ ω hω
    obtain ⟨x, hx, y, hy, hxy, hbad⟩ := hω
    exact ⟨x, hx, y, hy, hxy.trans_le hδ, hbad⟩
  · intro ε hε e' he'
    let B : ℕ → ℕ → Set Ω := fun k n => E (1 / ((k : ℝ) + 1)) (ε n)
    have hmono : ∀ k l n, k ≤ l → B l n ⊆ B k n := by
      intro k l n hkl ω hω
      obtain ⟨x, hx, y, hy, hxy, hbad⟩ := hω
      have hden : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hscale : 1 / ((l : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
        apply one_div_le_one_div_of_le hden
        have hc : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkl
        linarith
      exact ⟨x, hx, y, hy, hxy.trans_le hscale, hbad⟩
    have hdiag : ∀ ψ : ℕ → ℕ, StrictMono ψ →
        Tendsto (fun k => P (B k (ψ k))) atTop (𝓝 0) := by
      intro ψ hψ
      apply tendsto_oscillation_probability_of_prepared_compactness P K hK
        (fun n => F (ε (ψ n))) t ht
      · intro n
        exact hA (ε (ψ n)) (hε _).1 _
      · intro ξ hξ
        exact hcompact ε hε (ψ ∘ ξ) (hψ.comp hξ)
    obtain ⟨k, hk⟩ := @exists_fixed_scale_of_diagonal_probabilities Ω _ P B hmono hdiag e' he'
    exact ⟨1 / ((k : ℝ) + 1), by positivity, hk⟩

end MatedCRT
