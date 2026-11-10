import MatedCRT.Draft.Section2

/-!
# Truncated quenched laws, Step 7: vanishing cell mesh (fp-S3t-truncated-continuum, z10)

Source: notes/fp-gaps/CHATGPT-idla-3-4-truncated-laws.md, Step 7. Only the upper cell-diameter half of Lemma 2.8
(`CellSizeEstimateStmt`, BG20 Lemma 2.4) is used, at the enlarged inner radius `ρ₁ = (1 + ρ)/2`: with polynomially
high probability every cell of the mated-CRT map that meets `B_{ρ₁}(0)` has diameter at most `ε^α`,
`α = 2/(2+γ)² - ζ`. The event `MeshGood` is the one used by the walk-cell estimates of Step 9.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRT.TruncatedLaws

variable {Ω : Type} [MeasurableSpace Ω]

/-- The *mesh-good event* at scale `ε` (truncated-laws Step 7): every cell `H^ε_k = η([ε(k-1), εk])` meeting the
inner ball `B_{(1+ρ)/2}(0)` has diameter at most `ε^α`, where `α = 2/(2+γ)² - ζ`. -/
def MeshGood (S : MatedCRTEnv Ω) (γ ζ ρ : ℝ) (ε : ℝ) (ω : Ω) : Prop :=
  ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ((1 + ρ) / 2)).Nonempty →
    diam (cell ε (S.η ω) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ)

/-- **Step 7.** The mesh-bad events have probability tending to `0` as `ε ↓ 0`, by the upper half of
`CellSizeEstimateStmt` (Lemma 2.8, BG20 Lemma 2.4) at radius `(1 + ρ)/2`. -/
theorem meshBad_tendsto_zero {𝒮 : SpaceFillingSLEModel} (h28 : CellSizeEstimateStmt 𝒮) {γ ζ ρ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hζ0 : 0 < ζ) (hζγ : ζ < 2 / (2 + γ) ^ 2) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    Tendsto (fun ε : ℝ => S.P {ω | ¬ MeshGood S γ ζ ρ ε ω}) (𝓝[>] 0) (𝓝 0) := by
  have hζ1 : ζ < 1 := by
    have h2 : (2 : ℝ) ≤ (2 + γ) ^ 2 := by nlinarith
    have h3 : 2 / (2 + γ) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    linarith
  have hρ₁0 : 0 < (1 + ρ) / 2 := by linarith
  have hρ₁1 : (1 + ρ) / 2 < 1 := by linarith
  obtain ⟨p, hp, C, r₀, hr₀, hb⟩ := h28 γ hγ0 hγ2 ζ ((1 + ρ) / 2) hζ0 hζ1 hρ₁0 hρ₁1 Ω S hS
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (C * ε ^ p)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun ε : ℝ => C * ε ^ p) 0 :=
      continuousAt_const.mul (Real.continuousAt_rpow_const 0 p (Or.inr hp.le))
    have h0 : C * (0 : ℝ) ^ p = 0 := by rw [Real.zero_rpow hp.ne']; ring
    have h1 : Tendsto (fun ε : ℝ => C * ε ^ p) (𝓝[>] 0) (𝓝 0) := by
      have := hc.tendsto
      rw [h0] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h2 := ENNReal.tendsto_ofReal h1
    rwa [ENNReal.ofReal_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · exact Eventually.of_forall fun _ => zero_le
  · filter_upwards [Ioo_mem_nhdsGT hr₀] with ε hε
    refine (measure_mono ?_).trans (hb ε hε.1 hε.2)
    intro ω hω hE
    exact hω fun k hk => (hE k hk).2

end MatedCRT.TruncatedLaws
