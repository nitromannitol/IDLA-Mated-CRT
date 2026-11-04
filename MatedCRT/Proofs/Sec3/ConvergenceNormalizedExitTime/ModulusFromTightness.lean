import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.RandomSubsequenceProbability

/-! From random subsequential compactness to a probabilistic modulus. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology

/-- Random subsequential compactness after every measurable choice of scales
forces the oscillation probabilities at reciprocal scales to tend to zero. -/
theorem tendsto_oscillation_probability_of_random_compactness
    {Ω α : Type*} [mΩ : MeasurableSpace Ω] [PseudoMetricSpace α]
    (P : Measure Ω) [IsFiniteMeasure P] (m : MeasurableSpace Ω)
    (K : Set α) (hK : IsCompact K) (F : ℕ → Ω → α → ℝ)
    (t : ℝ) (ht : 0 < t)
    (hA : ∀ n : ℕ, MeasurableSet[m] {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < 1 / ((n : ℝ) + 1) ∧ t < |F n ω x - F n ω y|})
    (hAnull : ∀ n : ℕ, @NullMeasurableSet Ω mΩ {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < 1 / ((n : ℝ) + 1) ∧ t < |F n ω x - F n ω y|} P)
    (hcompact : ∀ I : Ω → ℕ → ℕ, (∀ n, Measurable[m] fun ω => I ω n) →
      (∀ ω n, n ≤ I ω n) → ∀ᵐ ω ∂P, ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∃ u : α → ℝ, ContinuousOn u K ∧
          TendstoUniformlyOn (fun k => F (I ω (φ k)) ω) u atTop K) :
    Tendsto (fun n : ℕ => P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < 1 / ((n : ℝ) + 1) ∧ t < |F n ω x - F n ω y|}) atTop (𝓝 0) := by
  let A : ℕ → Set Ω := fun n => {ω | ∃ x ∈ K, ∃ y ∈ K,
    dist x y < 1 / ((n : ℝ) + 1) ∧ t < |F n ω x - F n ω y|}
  refine @tendsto_measure_zero_of_random_subsequence Ω mΩ P ‹IsFiniteMeasure P› m A hA hAnull ?_
  intro I hI hIge
  filter_upwards [hcompact I hI hIge] with ω hω
  obtain ⟨φ, hφ, u, hu, hconv⟩ := hω
  refine ⟨φ, ?_⟩
  have hevent := eventually_small_oscillation_of_uniform_subsequence K hK
    (fun n => F (I ω n) ω) u φ hφ hu hconv ht
  filter_upwards [hevent] with k hk
  rintro ⟨x, hx, y, hy, hxy, hbad⟩
  have hden : (0 : ℝ) < (φ k : ℝ) + 1 := by positivity
  have hscale : 1 / ((I ω (φ k) : ℝ) + 1) ≤ 1 / ((φ k : ℝ) + 1) := by
    apply one_div_le_one_div_of_le hden
    have hcast : (φ k : ℝ) ≤ (I ω (φ k) : ℝ) := by exact_mod_cast hIge ω (φ k)
    linarith
  exact (not_lt_of_ge (hk x hx y hy (hxy.trans_le hscale)).le) hbad

end MatedCRT
