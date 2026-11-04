import MatedCRT.Proofs.LBM.GaussianSign

/-! Positive probability of immediate Brownian excursions. -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set HarmonicBalls MarkovProcess Filter Topology
open scoped ENNReal NNReal

/-- Planar Brownian motion has probability at least one half of making
arbitrarily early excursions in the positive real direction. -/
theorem planarBrownianMotion_real_frequently_above_initial_lower_bound (y : ℂ) :
    (1 / 2 : ℝ≥0∞) ≤ planarBrownianMotion y
      {b | ∃ᶠ t in 𝓝[>] (0 : ℝ≥0), y.re < (b t).re} := by
  let t : ℕ → ℝ≥0 := fun n => 1 / ((n : ℝ≥0) + 1)
  let E : ℕ → Set (ContinuousPath ℂ) := fun n =>
    ⋃ k ≥ n, {b | y.re < (b (t k)).re}
  have htime : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have htpos (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have hEmeas (n : ℕ) : MeasurableSet (E n) := by
    apply MeasurableSet.iUnion
    intro k
    apply MeasurableSet.iUnion
    intro _
    exact measurableSet_lt measurable_const
      (Complex.measurable_re.comp (ContinuousPath.continuous_eval (t k)).measurable)
  have hEanti : Antitone E := by
    intro n m hnm b hb
    simp only [E, mem_iUnion] at *
    obtain ⟨k, hkm, hb⟩ := hb
    exact ⟨k, hnm.trans hkm, hb⟩
  have hElower (n : ℕ) : (1 / 2 : ℝ≥0∞) ≤ planarBrownianMotion y (E n) := by
    rw [← planarBrownianMotion_real_increase_at_time y (t n) (ne_of_gt (htpos n))]
    apply measure_mono
    intro b hb
    simp only [E, mem_iUnion]
    exact ⟨n, le_rfl, hb⟩
  have hlim := tendsto_measure_iInter_atTop
    (μ := planarBrownianMotion y) (fun n => (hEmeas n).nullMeasurableSet) hEanti
    (show ∃ n, planarBrownianMotion y (E n) ≠ ⊤ from ⟨0, measure_ne_top _ _⟩)
  have hInter : (1 / 2 : ℝ≥0∞) ≤ planarBrownianMotion y (⋂ n, E n) :=
    ge_of_tendsto hlim (Eventually.of_forall hElower)
  refine hInter.trans (measure_mono ?_)
  intro b hb
  change ∃ᶠ t in 𝓝[>] (0 : ℝ≥0), y.re < (b t).re
  rw [(nhdsGT_basis (0 : ℝ≥0)).frequently_iff]
  intro a ha
  have hevent : ∀ᶠ n in atTop, t n < a := htime.eventually (Iio_mem_nhds ha)
  obtain ⟨n, hn⟩ := eventually_atTop.mp hevent
  have hb' := mem_iInter.mp hb n
  simp only [E, mem_iUnion] at hb'
  obtain ⟨k, hk, hbk⟩ := hb'
  exact ⟨t k, ⟨htpos k, hn k hk⟩, hbk⟩

end MatedCRT
