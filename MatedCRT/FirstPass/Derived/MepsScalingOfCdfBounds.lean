import MatedCRT.External.SLE

/-!
# The scaling of `m_ε` from two bounds on the annealed exit-time distribution

`m_ε` (eq:meps, line 731) is the lower median of the annealed exit time of the embedded walk
`η(X^{0,ε})` from `B_{1/2}`. The bounds `C⁻¹ ε⁻¹ ≤ m_ε ≤ C ε⁻¹` of eq:meps-scaling (Berestycki-Gwynne
arXiv:2003.10320 (1.8)) follow from two bounds on the annealed distribution function
`F_ε(s) = E[P^{h,η}(τ ≤ s)]` at times of order `ε⁻¹`, with constants depending only on `γ`:
`F_ε(c₁ ε⁻¹) < 1/2` (the walk does not leave `B_{1/2}` too fast, a consequence of the equicontinuity
of the rescaled walk, BG20 Proposition 6.5) and `F_ε(c₂ ε⁻¹) ≥ 1/2` (the exit time is not too large, a
consequence of the expected exit time bound, BG20 Proposition 5.1).

## Main results

* `MatedCRTEnv.mεCdf`: the annealed distribution function `F_ε`, with `S.mε ε = medianOf (S.mεCdf ε)`.
* `MatedCRTEnv.mεCdf_mono`: `F_ε` is monotone.
* `medianOf_le_of_half_le`, `le_medianOf_of_lt_half`: the lower median from one value of a monotone
  distribution function on each side of `1/2`.
* `mepsScalingInput_of_cdf_bounds`: `MepsScalingInput 𝒮` from the two bounds on `F_ε`.
-/

open MeasureTheory Metric
open scoped ENNReal

namespace MatedCRT

/-- The annealed distribution function `F_ε(s) = E[P^{h,η}(τ ≤ s)]` of the exit time of the embedded
walk `η(X^{0,ε})` from `B_{1/2}`, the walk being started from `a^ε_0` (eq:meps, line 731). -/
noncomputable def MatedCRTEnv.mεCdf {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ε : ℝ)
    (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) 0)
    {x | (embeddedExitTime ε (S.η ω) (ball 0 (1 / 2)) x : ℝ≥0∞) ≤ ENNReal.ofReal s} ∂S.P

theorem MatedCRTEnv.mε_eq_medianOf_mεCdf {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ε : ℝ) : S.mε ε = medianOf (S.mεCdf ε) :=
  rfl

/-- The annealed exit-time distribution function is monotone. -/
theorem MatedCRTEnv.mεCdf_mono {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ε : ℝ) :
    Monotone (S.mεCdf ε) := by
  intro s t hst
  refine lintegral_mono fun ω => measure_mono fun x hx => ?_
  exact le_trans hx (ENNReal.ofReal_le_ofReal hst)

/-- The lower median is at most every nonnegative time at which the distribution function has
reached `1/2`. -/
theorem medianOf_le_of_half_le {cdf : ℝ → ℝ≥0∞} {m : ℝ} (hm : 0 ≤ m)
    (h : (1 / 2 : ℝ≥0∞) ≤ cdf m) : medianOf cdf ≤ m :=
  csInf_le ⟨0, fun _ hx => hx.1⟩ ⟨hm, h⟩

/-- The lower median of a monotone distribution function that reaches `1/2` is at least every time
at which the distribution function is below `1/2`. -/
theorem le_medianOf_of_lt_half {cdf : ℝ → ℝ≥0∞} (hmono : Monotone cdf) {m : ℝ}
    (h : cdf m < 1 / 2) (hfin : ∃ x, 0 ≤ x ∧ (1 / 2 : ℝ≥0∞) ≤ cdf x) : m ≤ medianOf cdf := by
  refine le_csInf hfin fun x hx => ?_
  by_contra hlt
  exact absurd (hx.2.trans (hmono (le_of_not_ge hlt))) (not_le.2 h)

/-- **Scaling of `m_ε` from the annealed exit-time distribution** (eq:meps-scaling; BG20 (1.8)). If for
every `γ ∈ (0, 2)` there are `c₁, c₂ > 0`, depending only on `γ`, such that for every valid environment
and all small `ε`, `F_ε(c₁ ε⁻¹) < 1/2 ≤ F_ε(c₂ ε⁻¹)`, then `C⁻¹ ε⁻¹ ≤ m_ε ≤ C ε⁻¹` with
`C = max(c₂, c₁⁻¹, 2)`. -/
theorem mepsScalingInput_of_cdf_bounds {𝒮 : SpaceFillingSLEModel}
    (h : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
          S.mεCdf ε (c₁ * ε⁻¹) < 1 / 2 ∧ 1 / 2 ≤ S.mεCdf ε (c₂ * ε⁻¹)) :
    MepsScalingInput 𝒮 := by
  intro γ hγ hγ2
  obtain ⟨c₁, c₂, hc₁, hc₂, hS⟩ := h γ hγ hγ2
  set C : ℝ := max (max c₂ c₁⁻¹) 2 with hC
  have hC1 : 1 < C := lt_of_lt_of_le one_lt_two (le_max_right _ _)
  have hC0 : 0 < C := one_pos.trans hC1
  refine ⟨C, hC1, fun Ω _ S hSv => ?_⟩
  obtain ⟨ε₀, hε₀, hb⟩ := hS Ω S hSv
  refine ⟨ε₀, hε₀, fun ε hε hεε₀ => ?_⟩
  obtain ⟨hlow, hup⟩ := hb ε hε hεε₀
  have hεi : 0 < ε⁻¹ := inv_pos.2 hε
  have hupm : S.mε ε ≤ c₂ * ε⁻¹ :=
    medianOf_le_of_half_le (mul_pos hc₂ hεi).le hup
  have hlowm : c₁ * ε⁻¹ ≤ S.mε ε :=
    le_medianOf_of_lt_half (S.mεCdf_mono ε) hlow ⟨c₂ * ε⁻¹, (mul_pos hc₂ hεi).le, hup⟩
  have hc₂C : c₂ ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hc₁C : c₁⁻¹ ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hCc₁ : C⁻¹ ≤ c₁ := by
    rw [inv_le_comm₀ hC0 hc₁]
    exact hc₁C
  exact ⟨(mul_le_mul_of_nonneg_right hCc₁ hεi.le).trans hlowm,
    hupm.trans (mul_le_mul_of_nonneg_right hc₂C hεi.le)⟩

end MatedCRT
