import MatedCRT.Steps.Sec6.ConstantOrderLowerBoundDiv
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.OfSteps

/-! Relating the fixed and logarithmic survival estimates. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- The fixed-rate Lemma 6.8 statement implies its logarithmic-loss form, so
the logarithmic shell iteration also applies to the frozen draft hypothesis. -/
theorem constantOrderLowerBoundDivLog_of_fixed
    (𝒮 : SpaceFillingSLEModel) (h : ConstantOrderLowerBoundDivStmt 𝒮) :
    ConstantOrderLowerBoundDivLogStmt 𝒮 := by
  intro γ hγ hγ₂ ρ hρ hρ₁ βm hβm
  obtain ⟨ω₀, hω₀, hω⟩ := h γ hγ hγ₂ ρ hρ hρ₁ βm hβm
  refine ⟨ω₀, hω₀, ?_⟩
  intro s₀ hs₀ hs₀₁
  obtain ⟨s₁, s₂, hs₁, hs₁₁, hs₂, hs₂₁, hs⟩ := hω s₀ hs₀ hs₀₁
  refine ⟨s₁, s₂, hs₁, hs₁₁, hs₂, hs₂₁, ?_⟩
  intro Ω _ S hS
  obtain ⟨dd, hdd, hddpos, hevent⟩ := hs Ω S hS
  refine ⟨dd, hdd, hddpos, hevent.mono_pos ?_⟩
  intro ε _ ω hgood r hr hrd Θ hclosure hball A hA hcount a ha
  have hlog : 1 ≤ (1 + |Real.log r|) ^ 2 := by
    have h := abs_nonneg (Real.log r)
    nlinarith
  have hrate : s₂ / (1 + |Real.log r|) ^ 2 ≤ s₂ := by
    exact (div_le_self hs₂.le (by linarith))
  exact (hgood r hr hrd Θ hclosure hball A hA hcount a ha).trans
    (ENNReal.ofReal_le_ofReal (by linarith))

end MatedCRT.Sec7
