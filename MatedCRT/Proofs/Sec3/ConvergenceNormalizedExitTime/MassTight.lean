import MatedCRT.Proofs.Sec5.LLowerBound.ProperProb

/-!
# Tightness of the mass of a fixed ball

Area parametrization bounds its mass by the length of a time interval
containing all visits to the ball. The measurable escape events for the
space-filling curve therefore give a deterministic bound in probability.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- The mass of a fixed ball is bounded in probability. This does not require
the random measure to be measurable as a map into a space of measures. -/
theorem MatedCRTEnv.IsValid.tendsto_measure_large_ball_mass
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (ρ : ℝ) :
    Tendsto (fun n : ℕ => S.P {ω |
      ENNReal.ofReal (2 * ((n : ℝ) + 1)) < S.μ ω (ball 0 ρ)}) atTop (𝓝 0) := by
  have hescape := hS.tendsto_measure_curve_escape ρ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hescape
    (fun _ => zero_le) fun n => ?_
  apply measure_mono_ae
  filter_upwards [hS.isAreaParametrized] with ω hη
  intro hbad
  by_contra hno
  have hsub : ball (0 : ℂ) ρ ⊆ S.η ω '' Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) := by
    intro z hz
    obtain ⟨t, rfl⟩ := hη.2.2.1 z
    have ht : |t| < (n : ℝ) := by
      by_contra hn
      apply hno
      exact ⟨t, le_of_not_gt hn, by simpa [mem_ball, dist_zero_right] using hz⟩
    refine ⟨t, ?_, rfl⟩
    have ht' := abs_lt.1 ht
    constructor <;> linarith
  have hmass := hη.2.2.2 (-((n : ℝ) + 1)) ((n : ℝ) + 1) (by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith)
  have hle := measure_mono (μ := S.μ ω) hsub
  rw [hmass] at hle
  have heq : (n : ℝ) + 1 - (-((n : ℝ) + 1)) = 2 * ((n : ℝ) + 1) := by ring
  rw [heq] at hle
  exact (not_lt_of_ge hle) hbad

end MatedCRT
