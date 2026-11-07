import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.DyadicModulus

/-! Probability moduli from almost-sure boundary moduli. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- Almost-sure eventual exclusion at a random positive radius along each
dyadically dominated mesh sequence gives a deterministic probability modulus.
The bad events need only be null measurable. -/
theorem mesh_modulus_of_ae_dyadic_modulus
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (E : ℝ → ℝ → Set Ω)
    (hmono : ∀ δ δ' ε, δ ≤ δ' → E δ ε ⊆ E δ' ε)
    (hnull : ∀ δ ε : ℝ, 0 < ε → NullMeasurableSet (E δ ε) P)
    (hpath : ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n ∧ ε n < (1 / 2) ^ n) →
      ∀ᵐ ω ∂P, ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, ω ∉ E δ (ε n))
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
    apply tendsto_measure_zero_of_ae_eventually_not_mem P (fun k => B k (ψ k))
      (fun k => hnull _ _ (hε (ψ k)).1)
    filter_upwards [hpath ε hε] with ω hω
    obtain ⟨δ, hδ, hev⟩ := hω
    have hsmall : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < δ :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds hδ)
    have hsub : ∀ᶠ k in atTop, ω ∉ E δ (ε (ψ k)) := hψ.tendsto_atTop.eventually hev
    filter_upwards [hsmall, hsub] with k hk hn
    exact fun hbad => hn (hmono _ _ _ hk.le hbad)
  obtain ⟨k, hk⟩ := exists_fixed_scale_of_diagonal_probabilities P B hBmono hdiag he'
  exact ⟨1 / ((k : ℝ) + 1), by positivity, hk⟩

/-- A pathwise dyadic modulus between two sets yields the corresponding
boundary-pair probability modulus in the full positive mesh limit. -/
theorem mesh_boundary_pair_modulus_of_ae_dyadic_modulus
    {Ω α : Type*} [MeasurableSpace Ω] [PseudoMetricSpace α]
    (P : Measure Ω) [IsFiniteMeasure P] (K L : Set α) (F : ℝ → Ω → α → ℝ)
    (t : ℝ)
    (hnull : ∀ δ ε : ℝ, 0 < ε → NullMeasurableSet
      {ω | ∃ x ∈ K, ∃ y ∈ L, dist x y < δ ∧ t < |F ε ω x - F ε ω y|} P)
    (hpath : ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n ∧ ε n < (1 / 2) ^ n) →
      ∀ᵐ ω ∂P, ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
        ∀ x ∈ K, ∀ y ∈ L, dist x y ≤ δ → |F (ε n) ω x - F (ε n) ω y| ≤ t)
    {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      P {ω | ∃ x ∈ K, ∃ y ∈ L, dist x y < δ ∧ t < |F ε ω x - F ε ω y|} ≤ e := by
  apply mesh_modulus_of_ae_dyadic_modulus P
    (fun δ ε => {ω | ∃ x ∈ K, ∃ y ∈ L, dist x y < δ ∧ t < |F ε ω x - F ε ω y|})
    ?_ hnull ?_ he
  · intro δ δ' ε hδ ω hω
    obtain ⟨x, hx, y, hy, hxy, hbad⟩ := hω
    exact ⟨x, hx, y, hy, hxy.trans_le hδ, hbad⟩
  · intro ε hε
    filter_upwards [hpath ε hε] with ω ⟨δ, hδ, hω⟩
    refine ⟨δ, hδ, ?_⟩
    filter_upwards [hω] with n hn
    rintro ⟨x, hx, y, hy, hxy, hbad⟩
    exact (not_lt_of_ge (hn x hx y hy hxy.le)) hbad

end MatedCRT

#print axioms MatedCRT.mesh_modulus_of_ae_dyadic_modulus
#print axioms MatedCRT.mesh_boundary_pair_modulus_of_ae_dyadic_modulus
