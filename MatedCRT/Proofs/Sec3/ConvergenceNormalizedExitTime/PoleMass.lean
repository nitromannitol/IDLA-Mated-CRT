import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.TruncatedCells
import MatedCRT.Proofs.Sec5.LLowerBound.Mass

/-! # Mass near the pole of the Green function -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- The masses of closed balls around any point tend to zero along the
reciprocal natural-number radii. -/
theorem tendsto_measure_closedBall_reciprocal {μ : Measure ℂ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (x : ℂ) :
    Tendsto (fun n : ℕ => μ (closedBall x (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
  let s : ℕ → Set ℂ := fun n => closedBall x (1 / ((n : ℝ) + 1))
  have hs : Antitone s := by
    intro m n hmn
    apply closedBall_subset_closedBall
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hmn 1
  have hinter : ⋂ n, s n = {x} := by
    ext w
    simp only [mem_iInter, s, mem_closedBall, mem_singleton_iff]
    constructor
    · intro hw
      have hz : dist w x ≤ 0 :=
        ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat hw
      exact dist_eq_zero.mp (le_antisymm hz dist_nonneg)
    · intro hw
      subst w
      intro n
      simp only [dist_self]
      positivity
  have hfinite : ∃ n, μ (s n) ≠ ∞ := by
    refine ⟨0, ?_⟩
    apply ne_of_lt
    apply (measure_mono ?_).trans_lt (ball_mass_lt_top_of_proper hη hp x 2)
    simpa [s] using
      (closedBall_subset_ball (by norm_num : (1 : ℝ) < 2) : closedBall x 1 ⊆ ball x 2)
  have h := tendsto_measure_iInter_atTop
    (μ := μ) (s := s) (fun n => isClosed_closedBall.measurableSet.nullMeasurableSet) hs hfinite
  rw [hinter, measure_singleton_of_area_parametrized hη x] at h
  change Tendsto (fun n => μ (s n)) atTop (𝓝 0) at h
  exact h

end MatedCRT
