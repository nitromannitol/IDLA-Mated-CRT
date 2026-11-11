import MatedCRT.Draft.Section2
import MatedCRT.External.SLE

/-!
# Truncated quenched laws, Step 8: normalization error

Only the lower half of `MepsScalingInput` (the
Berestycki–Gwynne normalization (1.8)) is used: `m_ε ≥ C⁻¹ ε⁻¹`, hence `m_ε⁻¹ ≤ C ε → 0`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MatedCRT.TruncatedLaws

variable {Ω : Type} [MeasurableSpace Ω]

/-- **Step 8.** For a valid environment, `m_ε > 0` for small `ε` and `m_ε⁻¹ → 0` as `ε ↓ 0`. -/
theorem mepsInv_tendsto {𝒮 : SpaceFillingSLEModel} (hm : MepsScalingInput 𝒮) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ2 : γ < 2) (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < S.mε ε) ∧ Tendsto (fun ε : ℝ => (S.mε ε)⁻¹) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC1, hC⟩ := hm γ hγ0 hγ2
  obtain ⟨ε₀, hε₀, hb⟩ := hC Ω S hS
  have hCpos : 0 < C := by linarith
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 ε₀ := Ioo_mem_nhdsGT hε₀
  have hlow : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < C⁻¹ * ε⁻¹ ∧ C⁻¹ * ε⁻¹ ≤ S.mε ε := by
    filter_upwards [hev] with ε hε
    exact ⟨mul_pos (inv_pos.2 hCpos) (inv_pos.2 hε.1), (hb ε hε.1 hε.2).1⟩
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < S.mε ε := by
    filter_upwards [hlow] with ε hε
    exact lt_of_lt_of_le hε.1 hε.2
  have hupper : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (S.mε ε)⁻¹ ≤ C * ε := by
    filter_upwards [hlow] with ε hε
    calc (S.mε ε)⁻¹ ≤ (C⁻¹ * ε⁻¹)⁻¹ := inv_anti₀ hε.1 hε.2
      _ = C * ε := by rw [mul_inv, inv_inv, inv_inv]
  refine ⟨hpos, ?_⟩
  have hlinC : Tendsto (fun ε : ℝ => C * ε) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (fun x : ℝ => C * x) := continuous_const.mul continuous_id
    have := hcont.tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlinC ?_ hupper
  filter_upwards [hpos] with ε hε
  exact inv_nonneg.2 hε.le

end MatedCRT.TruncatedLaws
