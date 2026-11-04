import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.ModulusDiagonal

/-! Asymptotic moduli from random subsequential compactness. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- A random subsequential compactness estimate, stable under deterministic
and measurable random choices of indices, implies an asymptotic modulus in
probability on a compact set. -/
theorem asymptotic_modulus_of_random_compactness
    {Ω α : Type*} [mΩ : MeasurableSpace Ω] [PseudoMetricSpace α]
    (P : Measure Ω) [IsFiniteMeasure P] (m : MeasurableSpace Ω)
    (K : Set α) (hK : IsCompact K) (F : ℕ → Ω → α → ℝ)
    (t : ℝ) (ht : 0 < t)
    (hA : ∀ (n : ℕ) (δ : ℝ), MeasurableSet[m] {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < δ ∧ t < |F n ω x - F n ω y|})
    (hAnull : ∀ (n : ℕ) (δ : ℝ), @NullMeasurableSet Ω mΩ {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < δ ∧ t < |F n ω x - F n ω y|} P)
    (hcompact : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ I : Ω → ℕ → ℕ,
      (∀ n, Measurable[m] fun ω => I ω n) → (∀ ω n, n ≤ I ω n) →
      ∀ᵐ ω ∂P, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u : α → ℝ,
        ContinuousOn u K ∧ TendstoUniformlyOn (fun k => F (ψ (I ω (φ k))) ω) u atTop K)
    {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < δ ∧ t < |F n ω x - F n ω y|} ≤ e := by
  let E : ℕ → ℕ → Set Ω := fun k n => {ω | ∃ x ∈ K, ∃ y ∈ K,
    dist x y < 1 / ((k : ℝ) + 1) ∧ t < |F n ω x - F n ω y|}
  have hmono : ∀ k l n, k ≤ l → E l n ⊆ E k n := by
    intro k l n hkl ω hω
    obtain ⟨x, hx, y, hy, hxy, hbad⟩ := hω
    have hden : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hscale : 1 / ((l : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
      apply one_div_le_one_div_of_le hden
      have hc : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkl
      linarith
    exact ⟨x, hx, y, hy, hxy.trans_le hscale, hbad⟩
  have hdiag : ∀ ψ : ℕ → ℕ, StrictMono ψ →
      Tendsto (fun k => P (E k (ψ k))) atTop (𝓝 0) := by
    intro ψ hψ
    refine @tendsto_oscillation_probability_of_random_compactness Ω α mΩ _ P
      ‹IsFiniteMeasure P› m K hK (fun n => F (ψ n)) t ht ?_ ?_ ?_
    · intro n
      exact hA (ψ n) _
    · intro n
      exact hAnull (ψ n) _
    · exact hcompact ψ hψ
  obtain ⟨k, hk⟩ := @exists_fixed_scale_of_diagonal_probabilities Ω mΩ P E hmono hdiag e he
  exact ⟨1 / ((k : ℝ) + 1), by positivity, hk⟩

end MatedCRT
