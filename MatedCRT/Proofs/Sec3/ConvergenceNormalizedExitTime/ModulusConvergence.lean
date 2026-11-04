import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.FiniteNetConvergence

/-! Uniform convergence from pointwise convergence and a probabilistic modulus. -/

namespace MatedCRT

open Set Filter Topology MeasureTheory Metric _root_.HarmonicBalls
open scoped ENNReal

/-- On a compact set, pointwise convergence in probability and an asymptotic
modulus of continuity for the approximations and limit imply uniform convergence. -/
theorem uniformInProbability_of_asymptotic_modulus
    {Ω α : Type*} [MeasurableSpace Ω] [PseudoMetricSpace α]
    (P : Measure Ω) (D : Set α) (hD : IsCompact D)
    (F : ℝ → Ω → α → ℝ) (U : Ω → α → ℝ)
    (hpoint : ∀ x ∈ D, TendstoInProbability P (fun ε ω => F ε ω x) (fun ω => U ω x))
    (hmod : ∀ t : ℝ, 0 < t → ∀ e : ℝ≥0∞, 0 < e → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), P {ω | ∃ x ∈ D, ∃ y ∈ D, dist x y < δ ∧
        t < |F ε ω x - F ε ω y| + |U ω x - U ω y|} ≤ e) :
    ∀ t : ℝ, 0 < t → Tendsto (fun ε : ℝ => P {ω | ∃ x ∈ D,
      t < |F ε ω x - U ω x|}) (𝓝[>] 0) (𝓝 0) := by
  apply uniformInProbability_of_finite_anchors P D F U hpoint
  intro t ht e he
  obtain ⟨δ, hδ, hδmod⟩ := hmod t ht e he
  obtain ⟨A, hAD, hAf, hcov⟩ := (EMetric.totallyBounded_iff'.1 hD.totallyBounded)
    (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ)
  let K : Finset α := hAf.toFinset
  have hKD : ∀ x ∈ K, x ∈ D := by
    intro x hx
    exact hAD (hAf.mem_toFinset.mp hx)
  have hcover : ∀ x ∈ D, ∃ y ∈ K, dist x y < δ := by
    intro x hx
    obtain ⟨y, hyA, hxy⟩ := by simpa only [mem_iUnion, exists_prop] using hcov hx
    refine ⟨y, hAf.mem_toFinset.mpr hyA, ?_⟩
    have hxy' : ENNReal.ofReal (dist x y) < ENNReal.ofReal δ := by
      simpa only [Metric.mem_eball, edist_dist, dist_comm] using hxy
    exact (ENNReal.ofReal_lt_ofReal_iff hδ).mp hxy'
  refine ⟨K, hKD, ?_⟩
  filter_upwards [hδmod] with ε hε
  refine (measure_mono ?_).trans hε
  rintro ω ⟨x, hx, hbad⟩
  obtain ⟨y, hy, hdist⟩ := hcover x hx
  exact ⟨x, hx, y, hKD y hy, hdist, hbad y hy⟩

end MatedCRT
