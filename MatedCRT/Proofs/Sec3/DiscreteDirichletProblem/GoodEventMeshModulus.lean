import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.GoodEventModulus
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.PreparedMeshModulus

/-! # Mesh moduli under agreement on good events -/

namespace MatedCRT

open Set MeasureTheory Filter Topology
open scoped ENNReal

/-- A measurable representative with prepared random compactness transfers its
mesh modulus to a field that agrees with it on high-probability events. The
two error budgets are kept separate to permit arbitrary probability bounds. -/
theorem mesh_modulus_of_good_event_prepared_compactness
    {Ω α : Type*} [mΩ : MeasurableSpace Ω] [PseudoMetricSpace α]
    (P : Measure Ω) [IsFiniteMeasure P] (m : MeasurableSpace Ω)
    (K : Set α) (hK : IsCompact K) (F G : ℝ → Ω → α → ℝ)
    (E : ℝ → Set Ω) (t : ℝ) (ht : 0 < t)
    (hEq : ∀ ε, 0 < ε → ∀ᵐ ω ∂P, ω ∈ E ε → EqOn (F ε ω) (G ε ω) K)
    (hA : ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, ∃ A : Set Ω,
      MeasurableSet[m] A ∧ @NullMeasurableSet Ω mΩ A P ∧
      ∀ᵐ ω ∂P, (ω ∈ A ↔ ∃ x ∈ K, ∃ y ∈ K,
        dist x y < δ ∧ t < |G ε ω x - G ε ω y|))
    (hcompact : ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n ∧ ε n < (1 / 2) ^ n) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ I : Ω → ℕ → ℕ,
      (∀ n, Measurable[m] fun ω => I ω n) → (∀ ω n, n ≤ I ω n) →
      ∀ᵐ ω ∂P, ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ u : α → ℝ,
        ContinuousOn u K ∧ TendstoUniformlyOn
          (fun k => G (ε (φ (ψ (I ω (θ k))))) ω) u atTop K)
    {e₁ e₂ : ℝ≥0∞} (he₁ : 0 < e₁)
    (hbad : ∀ᶠ ε in 𝓝[>] (0 : ℝ), P (E ε)ᶜ ≤ e₂) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < δ ∧ t < |F ε ω x - F ε ω y|} ≤ e₁ + e₂ := by
  obtain ⟨δ, hδ, hG⟩ :=
    @mesh_modulus_of_prepared_random_compactness_versions Ω α mΩ _ P
      ‹IsFiniteMeasure P› m K hK G t ht hA hcompact e₁ he₁
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hG, hbad, self_mem_nhdsWithin] with ε hGε hbadε hε
  exact (@measure_oscillation_le_of_eqOn_good_event Ω α mΩ _ P (E ε) K (F ε) (G ε)
    (hEq ε hε) δ t).trans (add_le_add hGε hbadε)

end MatedCRT
