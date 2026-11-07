import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.BoundaryModulusProbability

/-! Boundary probability moduli after deterministic preparation. -/

namespace MatedCRT

open Set MeasureTheory Filter Topology
open scoped ENNReal

/-- A pathwise modulus on a deterministic subsequence of every rapidly
decreasing mesh sequence implies the full mesh probability modulus. -/
theorem mesh_modulus_of_prepared_dyadic_modulus
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (E : ℝ → ℝ → Set Ω)
    (hmono : ∀ δ δ' ε, δ ≤ δ' → E δ ε ⊆ E δ' ε)
    (hnull : ∀ δ ε : ℝ, 0 < ε → NullMeasurableSet (E δ ε) P)
    (hpath : ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n ∧ ε n < (1 / 2) ^ n) →
      ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ᵐ ω ∂P, ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, ω ∉ E δ (ε (ψ (φ n))))
    {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), P (E δ ε) ≤ e := by
  refine asymptotic_modulus_of_dyadic_mesh_sequences P E hmono ?_ he
  intro ε hε e' he'
  let B : ℕ → ℕ → Set Ω := fun k n => E (1 / ((k : ℝ) + 1)) (ε n)
  have hBmono : ∀ k l n, k ≤ l → B l n ⊆ B k n := by
    intro k l n hkl
    apply hmono
    apply one_div_le_one_div_of_le (by positivity)
    have hc : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkl
    linarith
  have hdiag : ∀ ψ : ℕ → ℕ, StrictMono ψ →
      Tendsto (fun k => P (B k (ψ k))) atTop (𝓝 0) := by
    intro ψ hψ
    apply Filter.tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨σ, hσ, hnsσ⟩ := strictMono_subseq_of_tendsto_atTop hns
    obtain ⟨φ, hφ, hp⟩ := hpath ε hε (ψ ∘ ns ∘ σ) (hψ.comp hnsσ)
    refine ⟨σ ∘ φ, ?_⟩
    apply tendsto_measure_zero_of_ae_eventually_not_mem P
      (fun k => B (ns (σ (φ k))) (ψ (ns (σ (φ k)))))
      (fun k => hnull _ _ (hε _).1)
    filter_upwards [hp] with ω ⟨δ, hδ, hev⟩
    have hsmall : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < δ :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds hδ)
    filter_upwards [hsmall, hev] with k hk hn
    have hscale : 1 / ((ns (σ (φ k)) : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right (hφ.id_le k |>.trans (hnsσ.id_le _)) 1
    exact fun hbad => hn (hmono _ _ _ (hscale.trans hk.le) hbad)
  obtain ⟨k, hk⟩ := exists_fixed_scale_of_diagonal_probabilities P B hBmono hdiag he'
  exact ⟨1 / ((k : ℝ) + 1), by positivity, hk⟩

end MatedCRT

#print axioms MatedCRT.mesh_modulus_of_prepared_dyadic_modulus
