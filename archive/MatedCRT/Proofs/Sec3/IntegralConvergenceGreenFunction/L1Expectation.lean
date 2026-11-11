import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.GaussianNormalization

/-! # Expectations under L¹ convergence -/

namespace MatedCRT

open MeasureTheory Filter Topology

/-- A constant expectation passes to an integrable limit under L¹ convergence. -/
theorem integral_eq_of_L1_limit {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (l : Filter ι) [NeBot l] (F : ι → Ω → ℝ) (f : Ω → ℝ)
    (c : ℝ) (hf : Integrable f P)
    (hF : ∀ᶠ i in l, Integrable (F i) P)
    (hmean : ∀ᶠ i in l, (∫ ω, F i ω ∂P) = c)
    (hconv : Tendsto (fun i => ∫ ω, |F i ω - f ω| ∂P) l (𝓝 0)) :
    (∫ ω, f ω ∂P) = c := by
  have hdiff : Tendsto (fun i => (∫ ω, F i ω ∂P) - ∫ ω, f ω ∂P) l (𝓝 0) := by
    apply squeeze_zero_norm' _ hconv
    filter_upwards [hF] with i hi
    rw [← integral_sub hi hf]
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω => F i ω - f ω)
  have hconst : Tendsto (fun i : ι => c - ∫ ω, f ω ∂P) l (𝓝 0) :=
    hdiff.congr' (hmean.mono fun i hi => by rw [hi])
  have : c - ∫ ω, f ω ∂P = 0 := tendsto_nhds_unique tendsto_const_nhds hconst
  linarith

end MatedCRT
