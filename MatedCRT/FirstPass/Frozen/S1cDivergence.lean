import MatedCRT.Defs.QuantumCone

/-!
# The radial-divergence input

`FrozenConeRadialDivergenceCorrected` states the radial divergence of the conditioned Brownian motion on its continuous-path carrier `ContinuousPath ℝ`; the transfer to the quantum cone is proved in `FirstPass/S1c/RadialDivergence.lean`.
-/

namespace MatedCRT

open MeasureTheory Filter Topology HarmonicBalls MarkovProcess
open scoped NNReal

/-- Radial divergence of the conditioned Brownian motion, on its continuous-path carrier. For `0 < γ < 2` and every probability `ν` on continuous paths with `IsBMConditionedPositive (lqgQ γ - γ) ν` (the conditioned Brownian motion with drift `c = Q - γ > 0`, where `Q = lqgQ γ`), `ν`-almost surely `w s + c s → ∞` as `s → ∞` on `ℝ≥0`.
Truth check: TRUE, as stated.
Source: Duplantier-Miller-Sheffield, *Mating of trees*, arXiv:1409.7055v4, Remark 4.4, printed pp. 74-75: the last-zero construction `X_s = B̃_{τ+s} + c(τ+s)` with `τ = sup {t ≥ 0 : B̃_t + c t = 0}` on p. 75, with the cone convention Definition 4.10, p. 79. Divergence follows from that construction and the Brownian strong law. For `c = Q - γ > 0` the conditioned process satisfies `(w_s + c s) / s → c` almost surely, hence `w_s / s → 0` almost surely. Downstream only the rational-time transfer is used (`FirstPass/S1c/RadialDivergence.lean`, `ae_ratDivergence_quantumConeRadialLaw`). -/
def FrozenConeRadialDivergenceCorrected : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ν : Measure (ContinuousPath ℝ), IsBMConditionedPositive (lqgQ γ - γ) ν →
    ∀ᵐ w ∂ν, Tendsto (fun s : ℝ≥0 => w s + (lqgQ γ - γ) * (s : ℝ)) atTop atTop

end MatedCRT
