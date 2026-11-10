import MatedCRT.Defs.Setting
import MatedCRT.Defs.Notation
import HarmonicBalls.Defs.Obstacle
import HarmonicBalls.Defs.Green

/-!
# The floor constant `FloorConstantStep` (task fp-S5d-5-1, floor note Part I, Steps 4-5; a named hypothesis)

`FloorConstantStep 𝒮` is the single input of `stoppedFloorCell_proved` (S5d/FloorProof.lean) that is not proved there:
the floor constant `s`, the bound `M` and their measurability for `S.fieldSigma`, with the floor on `B⁻_{δ/4}(Λ_t) \ {0}`
and the sup bound on `cl B_ρ`. It is kept in its own small file so that its discharge (FirstPass/S5o.lean, z2) can be
developed without importing the floor proof. Its docstring fixes the form that the discharge must prove.
-/

open MeasureTheory Filter Topology Set Metric HarmonicBalls

namespace MatedCRT

namespace FloorProof

/-- **The floor constant (floor note Part I, Steps 4-5; equations (7)-(13), with (11)-(12)).** For a valid environment `S`
with `γ ∈ (0,2)`, `ρ ∈ (0,1)`, a family `Λ` of cone harmonic balls a.s., `δ ∈ (0,ρ)` and `t > 0`, there are random variables
`s, M`, measurable for `S.fieldSigma`, with `0 < s ≤ 1` everywhere, such that a.s. on `{t < T}`:
`s ≤ α (W_t(x) + t G_{B_ρ}(0,x))` for `x ∈ B⁻_{δ/4}(Λ_t) \ {0}` and `|α W_t(x)| ≤ M` on `cl B_ρ`, where `α = c₀/6`,
`W_t = leastSupersolution (S.μ ω) ρ 0 t` and `G = greenFunction (B_ρ) 0`. Source: the measurable obstacle version
`StoppedFloorObstacleVersion` (FirstPass/S5k.lean, §4) and the strict gap `HarmonicBallStrictObstacleGapStep` ([C20]) feed
Steps 5.1-5.2 (`s` from `φ_ω`, (8)-(9); `M` from (12)), generic in FirstPass/S5l.lean; the discharge of this Prop is
FirstPass/S5o.lean (`floorConstantStep_proved`, fp-S5o, z2). Taken here as a named hypothesis. -/
def FloorConstantStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
    ∃ s M : Ω → ℝ, Measurable[S.fieldSigma] s ∧ Measurable[S.fieldSigma] M ∧
      (∀ ω, 0 < s ω ∧ s ω ≤ 1) ∧
      ∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ →
        (∀ x ∈ innerNbhd (δ / 4) (Λ ω t), x ≠ 0 →
          s ω ≤ S.c₀ / 6 * (_root_.HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t x +
            t * _root_.HarmonicBalls.greenFunction (ball (0 : ℂ) ρ) 0 x)) ∧
        (∀ x ∈ closedBall (0 : ℂ) ρ,
          |S.c₀ / 6 * _root_.HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t x| ≤ M ω)

end FloorProof

end MatedCRT
