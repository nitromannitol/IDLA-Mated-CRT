import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.MeasurableBadScales

/-! Turning random subsequence compactness into probability estimates. -/

namespace MatedCRT

open Set MeasureTheory Filter Topology

/-- If every measurable choice of increasingly late indices has an almost
sure subsequence that eventually avoids the chosen events, then the event
probabilities tend to zero. The choice is measurable for the specified
sub-sigma-algebra, while probabilities use the ambient sigma-algebra. -/
theorem tendsto_measure_zero_of_random_subsequence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (A : ℕ → Set Ω)
    (hA : ∀ n, MeasurableSet[m] (A n))
    (hsub : ∀ I : Ω → ℕ → ℕ, (∀ n, Measurable[m] fun ω => I ω n) →
      (∀ ω n, n ≤ I ω n) → ∀ᵐ ω ∂P, ∃ φ : ℕ → ℕ,
        ∀ᶠ k in atTop, ω ∉ A (I ω (φ k))) :
    Tendsto (fun n => P (A n)) atTop (𝓝 0) := by
  obtain ⟨I, hImeas, hIge, hIbad⟩ := @exists_measurable_bad_scale_selection Ω m A hA
  refine @tendsto_measure_zero_of_ae_eventually_not_mem Ω mΩ P ‹IsFiniteMeasure P› A ?_ ?_
  · intro n
    exact (hm _ (hA n)).nullMeasurableSet
  · filter_upwards [hsub I hImeas hIge] with ω hω
    by_contra hnot
    have hfrequent : ∀ n, ∃ j, n ≤ j ∧ ω ∈ A j := by
      intro n
      by_contra hnone
      apply hnot
      filter_upwards [eventually_ge_atTop n] with j hj
      intro hAj
      exact hnone ⟨j, hj, hAj⟩
    obtain ⟨φ, hφ⟩ := hω
    obtain ⟨k, hk⟩ := hφ.exists
    exact hk (hIbad ω (φ k) (hfrequent (φ k)))

end MatedCRT
