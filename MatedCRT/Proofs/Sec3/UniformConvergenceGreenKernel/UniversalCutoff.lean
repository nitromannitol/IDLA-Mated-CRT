import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.OccupationConvergence

/-! # Deterministic cutoffs for random Green occupation measures -/

namespace MatedCRT.GreenEnvironment

open MeasureTheory Filter Topology Set Metric
open scoped ContDiff

/-- The cutoff can be chosen before the curve and the measure: this permits
joint subsequence extraction for a countable family of deterministic tests. -/
theorem exists_universal_cutoff_for_occupation_error
    {U : Set ℂ} (hU : Bornology.IsBounded U) {f : ℂ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    ∃ φ : ℂ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      (∀ x, 0 ≤ φ x) ∧
      ∀ (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (η : ℝ → ℂ),
      IsAreaParametrized μ η → Tendsto η (cocompact ℝ) (cocompact ℂ) →
      ∀ δ > 0, ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
        ∀ t, 0 < t → ∀ (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ),
        (∀ b ∈ cellVertices ε η (tsupport f), matedDeg m b ≠ 0) →
        |(∫ x, f x * rescale t ε η (fun b => ε⁻¹ * greenKernel m A a b) x
          ∂degreeWeightedMeasure m ε η μ) -
          t⁻¹ * ∑' b : cellVertices ε η U, greenFn m A a b *
            f (vertexPoint ε η b)| ≤
        δ * (t⁻¹ * ∑' b : cellVertices ε η U, greenFn m A a b *
          φ (vertexPoint ε η b)) := by
  obtain ⟨r, hr⟩ := hfc.isCompact.isBounded.subset_ball (0 : ℂ)
  obtain ⟨φ, hφs, hφc, hφn, hφone⟩ :=
    exists_smooth_cutoff_one_on_closedBall (|r| + 2) (by positivity)
  refine ⟨φ, hφs, hφc, hφn, ?_⟩
  intro μ _ η hη hp δ hδ
  obtain ⟨ε₁, hε₁, hsmall⟩ := cell_diam_small_of_proper hη.1 hp r 1 zero_lt_one
  obtain ⟨ε₂, hε₂, hosc⟩ := exists_small_cells_test_oscillation hη.1 hp hf hfc hδ
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro ε hε hε₀ t ht m A a hdeg
  have hε₁' : ε < ε₁ := lt_of_lt_of_le hε₀ (min_le_left _ _)
  have hε₂' : ε < ε₂ := lt_of_lt_of_le hε₀ (min_le_right _ _)
  have hF := Tightness.cellVertices_finite hη.1 hp hε hfc.isCompact.isBounded
  let F := hF.toFinset
  have hC := Tightness.cellVertices_finite hη.1 hp hε hU
  apply abs_integral_sub_occupation_le_cutoff hη hp hε ht m A _ hC a hf hfc hδ.le F
  · intro b hb
    obtain ⟨x, hx, hxf⟩ := hF.mem_toFinset.mp hb
    exact ⟨x, hx, hfU hxf⟩
  · intro b hb
    exact hF.mem_toFinset.mpr hb
  · intro b hb
    exact hdeg b (hF.mem_toFinset.mp hb)
  · intro b hb x hx
    exact hosc ε hε hε₂' b (hF.mem_toFinset.mp hb) x hx
  · intro b hb
    exact hφn _
  · intro b hb
    obtain ⟨x, hx, hxf⟩ := hF.mem_toFinset.mp hb
    have hb' : b ∈ cellVertices ε η (ball 0 r) := ⟨x, hx, hr hxf⟩
    have hc : IsCompact (cell ε η b) := isCompact_Icc.image hη.1
    have hd := dist_le_diam_of_mem hc.isBounded (Tightness.vertexPoint_mem_cell hε b) hx
    have hdiam := hsmall ε hε hε₁' b hb'
    have hx' : dist x 0 < r := hr hxf
    have htri := dist_triangle (vertexPoint ε η b) x 0
    have hv : vertexPoint ε η b ∈ closedBall 0 (|r| + 2) := by
      change dist (vertexPoint ε η b) 0 ≤ |r| + 2
      have hrr := le_abs_self r
      linarith
    rw [hφone _ hv]

/-- Along a mesh sequence, convergence of the test and cutoff occupation
sums implies convergence of the degree-weighted kernel integral. -/
theorem exists_cutoff_for_integral_convergence
    {U : Set ℂ} (hU : Bornology.IsBounded U) {f : ℂ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    ∃ φ : ℂ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      ∀ (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (η : ℝ → ℂ),
      IsAreaParametrized μ η → Tendsto η (cocompact ℝ) (cocompact ℂ) →
      ∀ (ε t : ℕ → ℝ) (m : ℕ → ℤ → ℤ → ℕ) (A : ℕ → Set ℤ) (a : ℕ → ℤ),
      Tendsto ε atTop (𝓝[>] 0) →
      (∀ᶠ n in atTop, 0 ≤ t n ∧
        ∀ b ∈ cellVertices (ε n) η (tsupport f), matedDeg (m n) b ≠ 0) →
      ∀ y c : ℝ,
      Tendsto (fun n => (t n)⁻¹ * ∑' b : cellVertices (ε n) η U,
        greenFn (m n) (A n) (a n) b * f (vertexPoint (ε n) η b)) atTop (𝓝 y) →
      Tendsto (fun n => (t n)⁻¹ * ∑' b : cellVertices (ε n) η U,
        greenFn (m n) (A n) (a n) b * φ (vertexPoint (ε n) η b)) atTop (𝓝 c) →
      Tendsto (fun n => ∫ x, f x * rescale (t n) (ε n) η
        (fun b => (ε n)⁻¹ * greenKernel (m n) (A n) (a n) b) x
          ∂degreeWeightedMeasure (m n) (ε n) η μ) atTop (𝓝 y) := by
  obtain ⟨φ, hφs, hφc, _, hcut⟩ := exists_universal_cutoff_for_occupation_error hU hf hfc hfU
  refine ⟨φ, hφs, hφc, ?_⟩
  intro μ _ η hη hp ε t m A a hε hdeg y c hy hc
  apply tendsto_of_eventually_abs_sub_le hy hc
  intro δ hδ
  obtain ⟨ε₀, hε₀, hbound⟩ := hcut μ η hη hp δ hδ
  have hεpos : ∀ᶠ n in atTop, 0 < ε n := hε.eventually self_mem_nhdsWithin
  have hεsmall : ∀ᶠ n in atTop, ε n < ε₀ :=
    hε.eventually (nhdsWithin_le_nhds (Iio_mem_nhds hε₀))
  filter_upwards [hεpos, hεsmall, hdeg] with n hn hn' hdn
  by_cases htzero : t n = 0
  · simp [htzero, rescale]
  · exact hbound (ε n) hn hn' (t n) (lt_of_le_of_ne hdn.1 (Ne.symm htzero))
      (m n) (A n) (a n) hdn.2

end MatedCRT.GreenEnvironment
