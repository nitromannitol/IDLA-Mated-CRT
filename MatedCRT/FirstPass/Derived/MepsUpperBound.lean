import MatedCRT.FirstPass.Derived.LargestExitTimeFactor
import MatedCRT.FirstPass.Derived.MepsScalingOfCdfBounds

/-!
# The upper half of the scaling of `m_ε` as a bound on the median (Berestycki–Gwynne (2020), (1.8))

`mε_le_of_exitTimeUpper`: from the exit-time upper bound (Lemma 2.18) and the boundedness of the largest
exit-time variable (Lemma 2.17) there is `c₂ = c₂(γ) > 0` with `m_ε ≤ c₂ ε⁻¹` for all small `ε`, for every valid
environment.  It is the median form of the distribution-function bound `F_ε(c₂ ε⁻¹) ≥ 1/2`.
-/

open MeasureTheory

namespace MatedCRT

/-- **Upper bound for `m_ε`**: for `γ ∈ (0, 2)` there is `c₂ > 0` such that, for every valid environment `S`,
`m_ε ≤ c₂ ε⁻¹` for all sufficiently small `ε > 0`. -/
theorem mε_le_of_exitTimeUpper {𝒮 : SpaceFillingSLEModel} (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → S.mε ε ≤ c₂ * ε⁻¹ := by
  obtain ⟨c₂, hc₂, hS⟩ := mεCdf_upper h218 h217 hγ hγ2
  refine ⟨c₂, hc₂, fun Ω _ S hSv => ?_⟩
  obtain ⟨ε₀, hε₀, hε⟩ := hS Ω S hSv
  refine ⟨ε₀, hε₀, fun ε hε0 hεε₀ => ?_⟩
  rw [MatedCRTEnv.mε_eq_medianOf_mεCdf]
  exact medianOf_le_of_half_le (mul_nonneg hc₂.le (inv_nonneg.2 hε0.le)) (hε ε hε0 hεε₀)

end MatedCRT
