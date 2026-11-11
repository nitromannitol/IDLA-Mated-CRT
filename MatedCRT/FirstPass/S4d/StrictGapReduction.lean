import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.Final

/-!
# FIRST PASS, Proposition 4.2: reduction of `HarmonicBallStrictObstacleGapStep` to two named steps

The strict obstacle gap `HarmonicBallStrictObstacleGapStep` (Proofs/Sec4/DivSandpileLowerBound/Final.lean:32) splits
into two steps:

1. `StrictGapDeterministicComparisonStep`: on one realization of the cone family,
   `Λ_s ⊆ 𝒞_t` (the unregularized obstacle cluster) for `0 < s < t < T_ρ`. Deterministic; it uses the obstacle
   PDE, the minimum principle and the connectedness of `Λ_s` (`SatisfiesHarmonicBallConditions.isConnected`).
2. `StrictGapFixedTimeUnionStep`: for each deterministic `t > 0`, almost surely
   `Λ_t = ⋃_{0<s<t} Λ_s`. Its probabilistic core is `strictGapJump_null_of_const` (S4d/JumpTimes.lean), which needs
   the scaling identity of IDLA Lemma 2.6 (`ConeScaleInvarianceStmt`) transported to the jump event, and the
   measurability of the jump event for the given (arbitrary) family.

This file proves that the two steps imply `HarmonicBallStrictObstacleGapStep`. Neither step is proved here.
-/

namespace MatedCRT

open MeasureTheory Set Filter

/-- **Deterministic comparison (Armitage-Gardiner style minimum principle).** For one
realization `Λ` of the cone family for `μ`, and `0 < s < t` with `t < clusterExitTime Λ ρ` (so `Λ_t ⊆ B_{ρ/3}`),
the earlier harmonic ball lies in the unregularized obstacle cluster of `μ` in `B_ρ` at time `t`. -/
def StrictGapDeterministicComparisonStep : Prop :=
  ∀ (μ : Measure ℂ) (Λ : ℝ → Set ℂ), IsConeHarmonicBallFamily μ Λ →
    ∀ ρ : ℝ, 0 < ρ → ∀ s t : ℝ, 0 < s → s < t → t < clusterExitTime Λ ρ →
      Λ s ⊆ _root_.HarmonicBalls.cluster μ ρ 0 t

/-- **Fixed-time union.** For every deterministic `t > 0`, almost surely the
harmonic ball at `t` is the union of the earlier ones: `Λ_t = ⋃_{0<s<t} Λ_s`. The family is arbitrary, subject only
to the almost sure cone-family property (as in `HarmonicBallStrictObstacleGapStep`). -/
def StrictGapFixedTimeUnionStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
    ∀ t : ℝ, 0 < t → ∀ᵐ ω ∂S.P, Λ ω t = ⋃ s ∈ Ioo (0 : ℝ) t, Λ ω s

/-- **The strict obstacle gap from its two steps.** For `0 < s < t < T_ρ`, `Λ_s ⊆ 𝒞_t` by the
deterministic comparison, and `Λ_t = ⋃_{0<s<t} Λ_s` almost surely by the fixed-time union; hence `Λ_t ⊆ 𝒞_t` almost
surely on `{t < T_ρ}`, which is `HarmonicBallStrictObstacleGapStep`. -/
theorem harmonicBallStrictObstacleGapStep_of_steps (𝒮 : SpaceFillingSLEModel)
    (hdet : StrictGapDeterministicComparisonStep) (hnj : StrictGapFixedTimeUnionStep 𝒮) :
    HarmonicBallStrictObstacleGapStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ t ht
  filter_upwards [hΛ, hnj γ hγ hγ2 Ω S hS Λ hΛ t ht] with ω hω hunion
  intro hexit
  rw [hunion]
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
  exact hdet (S.μ ω) (Λ ω) hω ρ hρ s t hs.1 hs.2 hexit hxs

end MatedCRT
