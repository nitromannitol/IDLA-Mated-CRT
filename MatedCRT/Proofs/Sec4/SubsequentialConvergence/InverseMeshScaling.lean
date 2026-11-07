import MatedCRT.External.SLE
import MatedCRT.Proofs.Sec4.SubsequentialConvergence.QuantitativeHolderEventual

/-! Inverse median scaling along deterministic or pathwise mesh sequences. -/

namespace MatedCRT

open Filter Topology
open scoped NNReal

/-- The lower median scaling bound gives the upper bound on its inverse,
uniformly for all sufficiently small positive mesh sizes. -/
theorem inverse_median_scaling_of_mepsScaling
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    ∃ C : ℝ≥0, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      0 ≤ (S.mε ε)⁻¹ ∧ (S.mε ε)⁻¹ ≤ (C : ℝ) * ε := by
  obtain ⟨C, hC, hscale⟩ := hm γ hγ hγ2
  obtain ⟨ε₀, hε₀, hscale⟩ := hscale Ω S hS
  refine ⟨⟨C, by linarith⟩, ε₀, hε₀, ?_⟩
  intro ε hε hεsmall
  have hCpos : 0 < C := by linarith
  have hlower := (hscale ε hε hεsmall).1
  have hmpos : 0 < S.mε ε := lt_of_lt_of_le (mul_pos (inv_pos.mpr hCpos) (inv_pos.mpr hε)) hlower
  refine ⟨(inv_pos.mpr hmpos).le, ?_⟩
  have hi := inv_anti₀ (mul_pos (inv_pos.mpr hCpos) (inv_pos.mpr hε)) hlower
  rw [mul_inv_rev, inv_inv, inv_inv, mul_comm] at hi
  exact hi

/-- The inverse median scaling estimate holds eventually along every
positive sequence of mesh sizes tending to zero. -/
theorem eventually_inverse_median_scaling_of_mepsScaling
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    ∃ C : ℝ≥0, ∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
      ∀ᶠ n in atTop, 0 ≤ (S.mε (e n))⁻¹ ∧ (S.mε (e n))⁻¹ ≤ (C : ℝ) * e n := by
  obtain ⟨C, ε₀, hε₀, hbound⟩ := inverse_median_scaling_of_mepsScaling 𝒮 hm hγ hγ2 S hS
  refine ⟨C, fun e he he0 => ?_⟩
  filter_upwards [he0.eventually (gt_mem_nhds hε₀)] with n hn
  exact hbound (e n) (he n) hn

end MatedCRT
