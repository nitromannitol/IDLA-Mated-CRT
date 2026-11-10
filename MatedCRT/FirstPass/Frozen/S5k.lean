import MatedCRT.Defs.Setting

/-!
# Frozen external inputs of the measurable floor obstacle (task fp-S5k-5-1-floor-obstacle-version, worker z10)

Statements of external facts used by `MatedCRT/FirstPass/S5k*`. Each is a `Prop`-valued `def`, consumed as an explicit
hypothesis. Nothing here is proved in this repository.
-/

namespace MatedCRT

open MeasureTheory HarmonicBalls

/-- **FIRST-PASS FROZEN.** Least-supersolution membership for the LQG measure of a mated-CRT environment: almost surely,
for every radius `ρ ∈ (0,1)` and every `t > 0`, the continuum least supersolution `leastSupersolution (S.μ ω) ρ 0 t`
(pole `0`) belongs to `supersolutions (S.μ ω) ρ 0 t`, i.e. it is continuous on `B̄_ρ`, satisfies `Δw ≤ μ` on `B_ρ`
(`LaplacianLE`) and lies above the obstacle `-t G_{B_ρ}(0,·)` off the pole. Source: Bou-Rabee and Gwynne, "Harmonic balls in
Liouville quantum gravity", arXiv:2208.11795, Lemma 3.1 (`lemma:basic-properties`, printed line 621), in the form
`LeastSupersolutionMemStmt` (Harmonic-Balls-LQG `HarmonicBalls/Draft/Section3.lean`), applied to the `γ`-LQG measure
`S.μ` of the quantum cone `S.hC`, `S.hcirc` (`IsQuantumCone`, `IsLQGMeasure`, Setting.lean). The printed statement is for
the LQG measure of a whole-plane GFF; the transfer from the quantum cone to that setting is NOT checked here.
PENDING TRUTH CHECK (locator of the transfer from the cone to the whole-plane GFF: pending). Used by:
`isObstacleSolutionOn_leastSupersolution` (FirstPass/S5k/Identify.lean) and `stoppedFloorObstacleVersion_proved`
(FirstPass/S5k.lean). -/
def FrozenLeastSupersolutionMemCone (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ᵐ ω ∂S.P, ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ t : ℝ, 0 < t →
      leastSupersolution (S.μ ω) ρ 0 t ∈ supersolutions (S.μ ω) ρ 0 t

end MatedCRT
