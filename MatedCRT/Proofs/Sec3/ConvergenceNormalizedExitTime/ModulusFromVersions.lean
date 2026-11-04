import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.FullMeshCompactness

/-! Random compactness with almost-everywhere measurable event versions. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- Random compactness controls diagonal oscillations when each event has a
measurable version for the selecting sigma-algebra. -/
theorem tendsto_oscillation_probability_of_random_compactness_versions
    {Ω α : Type*} [mΩ : MeasurableSpace Ω] [PseudoMetricSpace α]
    (P : Measure Ω) [IsFiniteMeasure P] (m : MeasurableSpace Ω)
    (K : Set α) (hK : IsCompact K) (F : ℕ → Ω → α → ℝ)
    (t : ℝ) (ht : 0 < t)
    (hA : ∀ n : ℕ, ∃ A : Set Ω, MeasurableSet[m] A ∧
      @NullMeasurableSet Ω mΩ A P ∧ ∀ᵐ ω ∂P,
        (ω ∈ A ↔ ∃ x ∈ K, ∃ y ∈ K,
          dist x y < 1 / ((n : ℝ) + 1) ∧ t < |F n ω x - F n ω y|))
    (hcompact : ∀ I : Ω → ℕ → ℕ, (∀ n, Measurable[m] fun ω => I ω n) →
      (∀ ω n, n ≤ I ω n) → ∀ᵐ ω ∂P, ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∃ u : α → ℝ, ContinuousOn u K ∧
          TendstoUniformlyOn (fun k => F (I ω (φ k)) ω) u atTop K) :
    Tendsto (fun n : ℕ => P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < 1 / ((n : ℝ) + 1) ∧ t < |F n ω x - F n ω y|}) atTop (𝓝 0) := by
  classical
  choose A hAm hAn hAe using hA
  have hlim := @tendsto_measure_zero_of_random_subsequence Ω mΩ P ‹IsFiniteMeasure P›
    m A hAm hAn (by
      intro I hI hIge
      filter_upwards [hcompact I hI hIge, ae_all_iff.mpr hAe] with ω hω heq
      obtain ⟨φ, hφ, u, hu, hconv⟩ := hω
      refine ⟨φ, ?_⟩
      have hevent := eventually_small_oscillation_of_uniform_subsequence K hK
        (fun n => F (I ω n) ω) u φ hφ hu hconv ht
      filter_upwards [hevent] with k hk
      intro hmem
      obtain ⟨x, hx, y, hy, hxy, hbad⟩ := (heq (I ω (φ k))).mp hmem
      have hden : (0 : ℝ) < (φ k : ℝ) + 1 := by positivity
      have hscale : 1 / ((I ω (φ k) : ℝ) + 1) ≤ 1 / ((φ k : ℝ) + 1) := by
        apply one_div_le_one_div_of_le hden
        have hcast : (φ k : ℝ) ≤ (I ω (φ k) : ℝ) := by exact_mod_cast hIge ω (φ k)
        linarith
      exact (not_lt_of_ge (hk x hx y hy (hxy.trans_le hscale)).le) hbad)
  have heq : (fun n => P (A n)) = fun n : ℕ => P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < 1 / ((n : ℝ) + 1) ∧ t < |F n ω x - F n ω y|} := by
    funext n
    apply measure_congr
    filter_upwards [hAe n] with ω hω
    exact propext hω
  rwa [← heq]

/-- Measurable event versions suffice to obtain a full one-sided mesh modulus
from random subsequential compactness. -/
theorem mesh_modulus_of_random_compactness_versions
    {Ω α : Type*} [mΩ : MeasurableSpace Ω] [PseudoMetricSpace α]
    (P : Measure Ω) [IsFiniteMeasure P] (m : MeasurableSpace Ω)
    (K : Set α) (hK : IsCompact K) (F : ℝ → Ω → α → ℝ)
    (t : ℝ) (ht : 0 < t)
    (hA : ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, ∃ A : Set Ω,
      MeasurableSet[m] A ∧ @NullMeasurableSet Ω mΩ A P ∧
      ∀ᵐ ω ∂P, (ω ∈ A ↔ ∃ x ∈ K, ∃ y ∈ K,
        dist x y < δ ∧ t < |F ε ω x - F ε ω y|))
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
      refine @tendsto_oscillation_probability_of_random_compactness_versions Ω α mΩ _ P
        ‹IsFiniteMeasure P› m K hK (fun n => F (ε (ψ n))) t ht ?_ ?_
      · intro n
        exact hA (ε (ψ n)) (hε _) _
      · exact hcompact ε hε hlim ψ hψ
    obtain ⟨k, hk⟩ := @exists_fixed_scale_of_diagonal_probabilities Ω mΩ P B hmono hdiag e' he'
    exact ⟨1 / ((k : ℝ) + 1), by positivity, hk⟩

end MatedCRT
