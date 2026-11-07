import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.DyadicModulus

/-! Deterministic preparations suffice for full mesh-limit moduli. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- To prove a mesh-limit modulus, it suffices to find one deterministic
thinning with a sequence modulus for each dyadically dominated mesh sequence. -/
theorem asymptotic_modulus_of_prepared_dyadic_mesh_sequences
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (E : ℝ → ℝ → Set Ω)
    (hmono : ∀ δ δ' ε, δ ≤ δ' → E δ ε ⊆ E δ' ε)
    (hseq : ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n ∧ ε n < (1 / 2) ^ n) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ e : ℝ≥0∞, 0 < e → ∃ δ : ℝ, 0 < δ ∧
        ∀ᶠ n in atTop, P (E δ (ε (φ n))) ≤ e)
    {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), P (E δ ε) ≤ e := by
  classical
  by_contra hcontra
  have hbad : ∀ n : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε < (1 / 2 : ℝ) ^ n ∧
      e < P (E (1 / ((n : ℝ) + 1)) ε) := by
    intro n
    by_contra hnone
    apply hcontra
    refine ⟨1 / ((n : ℝ) + 1), by positivity, ?_⟩
    apply eventually_nhdsWithin_iff.mpr
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ)
      (show (0 : ℝ) < (1 / 2 : ℝ) ^ n by positivity)] with ε hε
    intro hεpos
    change (0 : ℝ) < ε at hεpos
    have hεlt : ε < (1 / 2 : ℝ) ^ n := by
      have := hε
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hεpos] at this
      exact this
    exact le_of_not_gt (fun hgt => hnone ⟨ε, hεpos, hεlt, hgt⟩)
  choose ε hε using hbad
  obtain ⟨φ, hφ, hseqφ⟩ := hseq ε (fun n => ⟨(hε n).1, (hε n).2.1⟩)
  obtain ⟨δ, hδ, hgood⟩ := hseqφ e he
  have hsmall := ((tendsto_one_div_add_atTop_nhds_zero_nat :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)).comp
      hφ.tendsto_atTop).eventually (Iio_mem_nhds hδ)
  obtain ⟨n, hn, hn'⟩ := (hsmall.and hgood).exists
  have hcompare : P (E (1 / (((φ n) : ℝ) + 1)) (ε (φ n))) ≤ P (E δ (ε (φ n))) :=
    measure_mono (hmono _ _ _ hn.le)
  exact (not_lt_of_ge (hcompare.trans hn')) (hε (φ n)).2.2

/-- Prepared random subsequential compactness and measurable oscillation
versions give a modulus in probability on the full mesh limit. -/
theorem mesh_modulus_of_prepared_random_compactness_versions
    {Ω α : Type*} [mΩ : MeasurableSpace Ω] [PseudoMetricSpace α]
    (P : Measure Ω) [IsFiniteMeasure P] (m : MeasurableSpace Ω)
    (K : Set α) (hK : IsCompact K) (F : ℝ → Ω → α → ℝ)
    (t : ℝ) (ht : 0 < t)
    (hA : ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, ∃ A : Set Ω,
      MeasurableSet[m] A ∧ @NullMeasurableSet Ω mΩ A P ∧
      ∀ᵐ ω ∂P, (ω ∈ A ↔ ∃ x ∈ K, ∃ y ∈ K,
        dist x y < δ ∧ t < |F ε ω x - F ε ω y|))
    (hcompact : ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n ∧ ε n < (1 / 2) ^ n) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ I : Ω → ℕ → ℕ,
      (∀ n, Measurable[m] fun ω => I ω n) → (∀ ω n, n ≤ I ω n) →
      ∀ᵐ ω ∂P, ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ u : α → ℝ,
        ContinuousOn u K ∧ TendstoUniformlyOn
          (fun k => F (ε (φ (ψ (I ω (θ k))))) ω) u atTop K)
    {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < δ ∧ t < |F ε ω x - F ε ω y|} ≤ e := by
  let E : ℝ → ℝ → Set Ω := fun δ ε => {ω | ∃ x ∈ K, ∃ y ∈ K,
    dist x y < δ ∧ t < |F ε ω x - F ε ω y|}
  refine @asymptotic_modulus_of_prepared_dyadic_mesh_sequences Ω mΩ P E ?_ ?_ e he
  · intro δ δ' ε hδ ω hω
    obtain ⟨x, hx, y, hy, hxy, hbad⟩ := hω
    exact ⟨x, hx, y, hy, hxy.trans_le hδ, hbad⟩
  · intro ε hε
    obtain ⟨φ, hφ, hcompactφ⟩ := hcompact ε hε
    refine ⟨φ, hφ, ?_⟩
    intro e' he'
    let B : ℕ → ℕ → Set Ω := fun k n => E (1 / ((k : ℝ) + 1)) (ε (φ n))
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
      refine @tendsto_oscillation_probability_of_random_compactness_versions Ω α mΩ _ P
        ‹IsFiniteMeasure P› m K hK (fun n => F (ε (φ (ψ n)))) t ht ?_ ?_
      · intro n
        exact hA (ε (φ (ψ n))) (hε _).1 _
      · exact hcompactφ ψ hψ
    obtain ⟨k, hk⟩ := @exists_fixed_scale_of_diagonal_probabilities Ω mΩ P B hmono hdiag e' he'
    exact ⟨1 / ((k : ℝ) + 1), by positivity, hk⟩

end MatedCRT
