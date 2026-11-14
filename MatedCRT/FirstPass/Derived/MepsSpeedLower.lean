import MatedCRT.FirstPass.Derived.MepsScalingOfLower
import MatedCRT.FirstPass.S6j.ExitTimeLowerTail
import MatedCRT.FirstPass.Closure.OwnBinderRewire
import MatedCRT.FirstPass.Derived.HBBallMassHolds

/-!
# A linear lower bound on the speed `m_ε` of the walk

The normalisation `m_ε` of eq:meps-scaling (Berestycki-Gwynne arXiv:2003.10320, (1.8)) is the lower median of the
annealed distribution of the exit time of the walk from `B_{1/2}`. For every valid environment it satisfies
`ε m_ε ≥ c₀ > 0` for all small `ε`. This is the form in which the speed enters estimates for the walk run at speed
`m_ε`: a time window of length `a` contains at least `c₀ a ε⁻¹` steps.

* `exists_le_mul_mε_of_mepsScalingInput`: from eq:meps-scaling, with `c₀ = C⁻¹`.
* `exists_le_mul_mε_of_lower`: from the lower half `F_ε(c₁ ε⁻¹) < 1/2` and Lemmas 2.17 and 2.18.
* `exists_le_mul_mε_of_uniformStart`: from Lemma 2.16 (Green kernel lower bound, BG20 Lemma 4.4), Lemma 2.18
  (exit-time moments, BG20 Proposition 5.1) and the uniform-start invariance principle (`GMS21UniformStartInput`,
  GMS21 Theorem 3.4); Lemma 2.17 is supplied by `firstPass_2_17_ownBinders` with its input proved.
-/

open Set Metric MeasureTheory Filter Topology HarmonicBalls

namespace MatedCRT.MepsSpeedLower

/-- **`ε m_ε` is bounded below** for a valid environment, given eq:meps-scaling: `C⁻¹ ε⁻¹ ≤ m_ε` gives
`C⁻¹ ≤ ε m_ε`. -/
theorem exists_le_mul_mε_of_mepsScalingInput {𝒮 : SpaceFillingSLEModel} (h : MepsScalingInput 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (hS : S.IsValid 𝒮 γ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → c₀ ≤ ε * S.mε ε := by
  obtain ⟨C, hC1, hC⟩ := h γ hγ hγ2
  obtain ⟨ε₀, hε₀, hb⟩ := hC Ω S hS
  have hC0 : 0 < C := one_pos.trans hC1
  refine ⟨C⁻¹, inv_pos.2 hC0, ε₀, hε₀, fun ε hε hεε₀ => ?_⟩
  have h1 : C⁻¹ * ε⁻¹ ≤ S.mε ε := (hb ε hε hεε₀).1
  calc C⁻¹ = ε * (C⁻¹ * ε⁻¹) := by field_simp
    _ ≤ ε * S.mε ε := mul_le_mul_of_nonneg_left h1 hε.le

/-- **`ε m_ε` is bounded below from the lower half of (1.8)**: given Lemmas 2.18 and 2.17 and, for every
`γ ∈ (0, 2)`, a constant `c₁ > 0` with `F_ε(c₁ ε⁻¹) < 1/2` for every valid environment and all small `ε`. -/
theorem exists_le_mul_mε_of_lower {𝒮 : SpaceFillingSLEModel} (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt)
    (hlow : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → S.mεCdf ε (c₁ * ε⁻¹) < 1 / 2)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (hS : S.IsValid 𝒮 γ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → c₀ ≤ ε * S.mε ε :=
  exists_le_mul_mε_of_mepsScalingInput (mepsScalingInput_of_lower h218 h217 hlow) hγ hγ2 S hS

/-- **`ε m_ε` is bounded below from the uniform-start invariance principle**: the lower half of (1.8) is
`ExitTimeLowerTail.mεCdf_lower_of_uniformStart` (Lemmas 2.16, 2.18 and `GMS21UniformStartInput`), and Lemma 2.17 is
proved (`firstPass_2_17_ownBinders` with the cone ball-mass input supplied). -/
theorem exists_le_mul_mε_of_uniformStart {𝒮 : SpaceFillingSLEModel}
    (h216 : GreenKernelLowerBoundStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (hS : S.IsValid 𝒮 γ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → c₀ ≤ ε * S.mε ε :=
  exists_le_mul_mε_of_lower h218
    (firstPass_2_17_ownBinders (hBG := FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds))
    (ExitTimeLowerTail.mεCdf_lower_of_uniformStart h216 h218 hN4) hγ hγ2 S hS

end MatedCRT.MepsSpeedLower
