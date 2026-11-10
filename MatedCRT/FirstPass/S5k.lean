import MatedCRT.Defs.Setting

/-!
# First pass: measurable version of the continuum floor obstacle (task fp-S5k-5-1-floor-obstacle-version, worker z10)

`StoppedFloorObstacleVersion 𝒮` is the conclusion of Part I, §4 of `notes/fp-gaps/CHATGPT-z5-floor.md` (end of Step 4.2,
equation (7)): a measurable version `Ŵ` of the continuum least supersolution `W_t = leastSupersolution (S.μ ω) ρ 0 t` of
the obstacle problem, on the event `{t < clusterExitTime (Λ ω) ρ}`, with every evaluation `ω ↦ Ŵ ω x` measurable for the
field σ-algebra `S.fieldSigma`, continuous on the closed disk `B̄_ρ`, and vanishing on its boundary for every `ω`.

The binders are those of `StoppedFloorCellStep` (S5d/FloorCellStep.lean:25) up to `t`; the parameter `δ` is not used by §4
and is omitted. The first commit contains only the definition; the theorem `stoppedFloorObstacleVersion_proved` is not
yet proved and is not in this file.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- **Measurable version of the continuum floor obstacle** (the conclusion of §4 of `notes/fp-gaps/CHATGPT-z5-floor.md`).
For `γ ∈ (0,2)`, `ρ ∈ (0,1)`, a valid mated-CRT environment `S` on `Ω`, a family `Λ` of cone harmonic balls a.s. and
`t > 0`, there is `Ŵ : Ω → ℂ → ℝ` such that: each evaluation `ω ↦ Ŵ ω x` is `S.fieldSigma`-measurable; for every `ω`, the map
`Ŵ ω` is continuous on `B̄_ρ` and vanishes on `∂B_ρ`; and for `P`-a.e. `ω` on the event `{t < clusterExitTime (Λ ω) ρ}`,
`Ŵ ω` agrees on `B̄_ρ` with the continuum least supersolution `W_t = leastSupersolution (S.μ ω) ρ 0 t`
(`HarmonicBalls.leastSupersolution`, the obstacle `-t G_{B_ρ}(0,·)`, Harmonic-Balls-LQG `HarmonicBalls/Defs/Obstacle.lean:63`).

The measurability is with respect to `S.fieldSigma`, not the ambient σ-algebra; no measurability of the raw expression
`leastSupersolution (S.μ ω) …` is asserted. Source: Part I, Step 4.2 and (7) of the floor note. -/
def StoppedFloorObstacleVersion (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ t : ℝ, 0 < t →
    ∃ What : Ω → ℂ → ℝ,
      (∀ x : ℂ, Measurable[S.fieldSigma] fun ω => What ω x) ∧
      (∀ ω, ContinuousOn (What ω) (closedBall (0 : ℂ) ρ)) ∧
      (∀ ω, ∀ x ∈ sphere (0 : ℂ) ρ, What ω x = 0) ∧
      (∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ →
        ∀ x ∈ closedBall (0 : ℂ) ρ,
          What ω x = _root_.HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t x)

end MatedCRT
