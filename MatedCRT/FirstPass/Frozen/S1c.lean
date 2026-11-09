import MatedCRT.Steps.Sec1.Convergence

/-!
# First pass: frozen external input of the scaled cluster exit time (q4, task fp-S1c-hT-and-composition)

`FrozenConeRadialDivergence` is the one general Brownian fact used by the lower-tail bound for the cone scale radius
`R_b` in the proof of `ScaledClusterExitTimeStep` (fleet note notes/fp-gaps/G-hT.md, Lemma 2). It concerns only the
radial part of the quantum cone (the conditioned Brownian motion `B̂` of Definition 2.1 and its quantum cone radial
law `quantumConeRadialLaw`), not harmonic balls, clusters or IDLA processes.
-/

namespace MatedCRT

open MeasureTheory Filter Topology HarmonicBalls MarkovProcess
open scoped NNReal

/-- FIRST-PASS FROZEN. Radial divergence of the conditioned process. For `0 < γ < 2` and every probability `ν` on
continuous paths which is the conditioned Brownian motion `B̂` of `IsBMConditionedPositive (Q - γ) ν` (drift
`c = Q - γ = 2/γ - γ/2 > 0`), `ν`-almost surely `B̂_s + c s → ∞` as `s → ∞` on `ℝ≥0`. In the coordinates of the quantum
cone radial law (`quantumConeRadialLaw γ ν`, second component `s ↦ B̂_s - γ s`), this reads: almost surely the
second path `x.2` satisfies `x.2 s + Q s → ∞`, with `Q = lqgQ γ`.
Source: the standard long-time behaviour of Brownian motion with positive drift conditioned to stay positive
(Doob h-transform of drifted Brownian motion killed at `0`; `Y_s / s → c` a.s.), as used for the conditioned process
of Duplantier–Miller–Sheffield (2014, *Mating of trees*, arXiv:1409.7055v4), Definition of the quantum cone
(the conditioned process `B̂` of the radial part); the identification of the weak limit `ν` of `IsBMConditionedPositive`
with the h-transform is part of this standard fact. Locator: standard; locator pending.
Used by: firstPassS1c_coneScaleRadius_lowerTail (MatedCRT/FirstPass/S1c.lean). -/
def FrozenConeRadialDivergence : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ν : Measure (ContinuousPath ℝ), IsBMConditionedPositive (lqgQ γ - γ) ν →
    ∀ᵐ x ∂(quantumConeRadialLaw γ ν),
      Tendsto (fun s : ℝ≥0 => x.2 s + lqgQ γ * (s : ℝ)) atTop atTop

end MatedCRT
