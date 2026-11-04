import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.TestOscillation

/-! # Uniform control of Green occupation integral errors -/

namespace MatedCRT.GreenEnvironment

open MeasureTheory Filter Topology Set Metric
open scoped ContDiff

/-- A single smooth cutoff controls the occupation error for every sufficiently
fine mesh, with an arbitrarily small coefficient. -/
theorem exists_cutoff_for_occupation_error
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {U : Set ℂ} (hU : Bornology.IsBounded U) {f : ℂ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    ∃ φ : ℂ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      (∀ x, 0 ≤ φ x) ∧ ∀ δ > 0, ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
        ∀ t, 0 < t → ∀ (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ),
        (∀ b ∈ cellVertices ε η (tsupport f), matedDeg m b ≠ 0) →
        |(∫ x, f x * rescale t ε η (fun b => ε⁻¹ * greenKernel m A a b) x
          ∂degreeWeightedMeasure m ε η μ) -
          t⁻¹ * ∑' b : cellVertices ε η U, greenFn m A a b *
            f (vertexPoint ε η b)| ≤
        δ * (t⁻¹ * ∑' b : cellVertices ε η U, greenFn m A a b *
          φ (vertexPoint ε η b)) := by
  obtain ⟨R, hR, ε₁, hε₁, hvertex⟩ :=
    exists_vertexPoint_bound_of_bounded hη.1 hp hfc.isCompact.isBounded
  obtain ⟨φ, hφs, hφc, hφn, hφone⟩ := exists_smooth_cutoff_one_on_closedBall R hR
  refine ⟨φ, hφs, hφc, hφn, ?_⟩
  intro δ hδ
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
    rw [hφone _ (hvertex ε hε hε₁' b (hF.mem_toFinset.mp hb))]

/-- An arbitrarily small error coefficient times a convergent cutoff mass
forces two sequences to have the same limit. -/
theorem tendsto_of_eventually_abs_sub_le {X Y B : ℕ → ℝ} {y b : ℝ}
    (hY : Tendsto Y atTop (𝓝 y)) (hB : Tendsto B atTop (𝓝 b))
    (herror : ∀ δ > 0, ∀ᶠ n in atTop, |X n - Y n| ≤ δ * B n) :
    Tendsto X atTop (𝓝 y) := by
  have hdiff : Tendsto (fun n => X n - Y n) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro e he
    let M := |b| + 1
    have hM : 0 < M := by dsimp [M]; positivity
    let δ := e / (2 * M)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hbound : ∀ᶠ n in atTop, B n < M :=
      hB.eventually (Iio_mem_nhds (by dsimp [M]; have := le_abs_self b; linarith))
    filter_upwards [herror δ hδ, hbound] with n hn hnB
    have hδM : δ * M = e / 2 := by dsimp [δ]; field_simp
    have hm : δ * B n < δ * M := mul_lt_mul_of_pos_left hnB hδ
    have hdist : |X n - Y n| < e := by linarith
    simpa only [Real.dist_eq, sub_zero] using hdist
  have h := hdiff.add hY
  simpa using h

end MatedCRT.GreenEnvironment
