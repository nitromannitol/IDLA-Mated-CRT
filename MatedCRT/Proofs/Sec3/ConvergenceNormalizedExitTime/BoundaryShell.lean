import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.PoleMass

/-! # Boundary-shell mass for truncated cell sums -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- Inside shells of an open ball have vanishing mass when the ball has
finite mass. No assumption on the mass of the boundary circle is needed. -/
theorem tendsto_measure_inside_ball_shell {μ : Measure ℂ} {z : ℂ} {r : ℝ}
    (hfinite : μ (ball z r) ≠ ∞) :
    Tendsto (fun n : ℕ => μ (ball z r \ ball z (r - 1 / ((n : ℝ) + 1))))
      atTop (𝓝 0) := by
  let s : ℕ → Set ℂ := fun n => ball z r \ ball z (r - 1 / ((n : ℝ) + 1))
  have hs : Antitone s := by
    intro m n hmn
    apply sdiff_subset_sdiff Subset.rfl
    apply ball_subset_ball
    have hdiv : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hmn 1
    linarith
  have hinter : ⋂ n, s n = ∅ := by
    apply Subset.antisymm ?_ (empty_subset _)
    intro w hw
    change False
    have hw' := mem_iInter.1 hw
    have hwr : dist w z < r := (hw' 0).1
    have hr : r ≤ dist w z := by
      have hlim : Tendsto (fun n : ℕ => r - 1 / ((n : ℝ) + 1)) atTop (𝓝 r) := by
        have hzero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have hc : Tendsto (fun _ : ℕ => r) atTop (𝓝 r) := tendsto_const_nhds
        simpa using hc.sub hzero
      apply le_of_tendsto' hlim
      intro n
      exact not_lt.1 (hw' n).2
    exact (not_lt_of_ge hr) hwr
  have hf : ∃ n, μ (s n) ≠ ∞ :=
    ⟨0, ne_top_of_le_ne_top hfinite (measure_mono sdiff_subset)⟩
  have h := tendsto_measure_iInter_atTop (μ := μ) (s := s)
    (fun _ => (measurableSet_ball.diff measurableSet_ball).nullMeasurableSet) hs hf
  rw [hinter, measure_empty] at h
  change Tendsto (fun n => μ (s n)) atTop (𝓝 0) at h
  exact h

/-- The measure of the part omitted by the truncated cell union is bounded by
an inside shell of the outer ball and a ball around the pole. -/
theorem measure_punctured_ball_sdiff_fill_le {μ : Measure ℂ} {η : ℝ → ℂ}
    {ε r δ d : ℝ} {z y : ℂ} (hη : Continuous η) (hsurj : Function.Surjective η)
    (hε : 0 < ε) (hd : 0 ≤ d)
    (hsmall : ∀ a ∈ cellVertices ε η (ball z r), diam (cell ε η a) ≤ d) :
    μ ((ball z r \ ball y δ) \
      fillCells ε η (interiorCellVertices ε η (ball z r) \ cellVertices ε η (ball y δ))) ≤
      μ (ball z r \ ball z (r - d)) + μ (closedBall y (δ + d)) := by
  calc
    _ ≤ μ ((ball z r \ ball z (r - d)) ∪ (closedBall y (δ + d) \ ball y δ)) :=
      measure_mono (punctured_ball_sdiff_fill_subset_shells hη hsurj hε hd hsmall)
    _ ≤ μ (ball z r \ ball z (r - d)) + μ (closedBall y (δ + d) \ ball y δ) :=
      measure_union_le _ _
    _ ≤ μ (ball z r \ ball z (r - d)) + μ (closedBall y (δ + d)) :=
      add_le_add le_rfl (measure_mono (sdiff_subset :
        closedBall y (δ + d) \ ball y δ ⊆ closedBall y (δ + d)))

/-- For a fixed proper area-parametrized curve, the truncation radius and a
cell-diameter threshold can be chosen so that the omitted mass is arbitrarily
small, uniformly over all meshes satisfying that diameter threshold. -/
theorem exists_truncation_small_discrepancy {μ : Measure ℂ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (z y : ℂ) (r : ℝ) {ρ : ℝ} (hρ : 0 < ρ) {τ : ℝ≥0∞} (hτ : 0 < τ) :
    ∃ δ d : ℝ, 0 < δ ∧ δ < ρ ∧ 0 < d ∧ ∀ ε : ℝ, 0 < ε →
      (∀ a ∈ cellVertices ε η (ball z r), diam (cell ε η a) ≤ d) →
      μ ((ball z r \ ball y δ) \
        fillCells ε η (interiorCellVertices ε η (ball z r) \ cellVertices ε η (ball y δ))) < τ := by
  have ho := tendsto_measure_inside_ball_shell (ball_mass_lt_top_of_proper hη hp z r).ne
  have hi := tendsto_measure_closedBall_reciprocal hη hp y
  have hsum : Tendsto (fun n : ℕ =>
      μ (ball z r \ ball z (r - 1 / ((n : ℝ) + 1))) +
      μ (closedBall y (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
    simpa using ho.add hi
  have hevent : ∀ᶠ n : ℕ in atTop,
      μ (ball z r \ ball z (r - 1 / ((n : ℝ) + 1))) +
      μ (closedBall y (1 / ((n : ℝ) + 1))) < τ :=
    hsum.eventually (Iio_mem_nhds hτ)
  have hzero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hsmallRadius : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ρ :=
    hzero.eventually (Iio_mem_nhds hρ)
  obtain ⟨n, hn, hnρ⟩ := (hevent.and hsmallRadius).exists
  let q : ℝ := 1 / ((n : ℝ) + 1)
  have hq : 0 < q := by dsimp [q]; positivity
  refine ⟨q / 2, q / 2, by positivity, by dsimp [q]; linarith, by positivity, ?_⟩
  intro ε hε hsmall
  have houter : μ (ball z r \ ball z (r - q / 2)) ≤ μ (ball z r \ ball z (r - q)) :=
    measure_mono (sdiff_subset_sdiff Subset.rfl (ball_subset_ball (by linarith)))
  calc
    _ ≤ μ (ball z r \ ball z (r - q / 2)) + μ (closedBall y (q / 2 + q / 2)) :=
      measure_punctured_ball_sdiff_fill_le hη.1 hη.2.2.1 hε (by positivity) hsmall
    _ ≤ μ (ball z r \ ball z (r - q)) + μ (closedBall y q) := by
      have : q / 2 + q / 2 = q := by ring
      rw [this]
      exact add_le_add houter le_rfl
    _ < τ := hn

end MatedCRT
