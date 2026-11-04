import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.FilterModulus

/-! A full mesh-limit modulus from random subsequential compactness. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- Random subsequential compactness along every positive mesh sequence gives
an asymptotic modulus on the full one-sided mesh limit, provided oscillation
events are measurable for the selecting sigma-algebra and null-measurable for
the probability law. -/
theorem mesh_modulus_of_random_compactness
    {Ω α : Type*} [mΩ : MeasurableSpace Ω] [PseudoMetricSpace α]
    (P : Measure Ω) [IsFiniteMeasure P] (m : MeasurableSpace Ω)
    (K : Set α) (hK : IsCompact K) (F : ℝ → Ω → α → ℝ)
    (t : ℝ) (ht : 0 < t)
    (hA : ∀ (ε : ℝ), 0 < ε → ∀ δ : ℝ,
      MeasurableSet[m] {ω | ∃ x ∈ K, ∃ y ∈ K,
        dist x y < δ ∧ t < |F ε ω x - F ε ω y|})
    (hAnull : ∀ (ε : ℝ), 0 < ε → ∀ δ : ℝ,
      @NullMeasurableSet Ω mΩ {ω | ∃ x ∈ K, ∃ y ∈ K,
        dist x y < δ ∧ t < |F ε ω x - F ε ω y|} P)
    (hcompact : ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ I : Ω → ℕ → ℕ,
      (∀ n, Measurable[m] fun ω => I ω n) → (∀ ω n, n ≤ I ω n) →
      ∀ᵐ ω ∂P, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u : α → ℝ,
        ContinuousOn u K ∧ TendstoUniformlyOn
          (fun k => F (ε (ψ (I ω (φ k)))) ω) u atTop K)
    {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < δ ∧ t < |F ε ω x - F ε ω y|} ≤ e := by
  let E : ℝ → ℝ → Set Ω := fun δ ε => {ω | ∃ x ∈ K, ∃ y ∈ K,
    dist x y < δ ∧ t < |F ε ω x - F ε ω y|}
  refine @asymptotic_modulus_of_mesh_sequences Ω mΩ P E ?_ ?_ e he
  · intro δ δ' ε hδ ω hω
    obtain ⟨x, hx, y, hy, hxy, hbad⟩ := hω
    exact ⟨x, hx, y, hy, hxy.trans_le hδ, hbad⟩
  · intro ε hε hlim e' he'
    refine @asymptotic_modulus_of_random_compactness Ω α mΩ _ P ‹IsFiniteMeasure P›
      m K hK (fun n => F (ε n)) t ht ?_ ?_ ?_ e' he'
    · intro n δ
      exact hA (ε n) (hε n) δ
    · intro n δ
      exact hAnull (ε n) (hε n) δ
    · exact hcompact ε hε hlim

end MatedCRT
