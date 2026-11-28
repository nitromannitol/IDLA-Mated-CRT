import HarmonicBalls.Proofs.Sec6.BrownianAvoidance

/-!
# The probability of leaving an open set before hitting a compact set

For an open set `O`, a compact set `K` and a point `x ∈ ℂ`, `avoidanceProb O K x` is the probability that planar
Brownian motion started at `x` leaves `O` no later than it hits `K`, that is, of the event
`ContinuousPath.exitTime O ≤ ContinuousPath.exitTime Kᶜ` (`avoidEvent O K`). It is a measurable function of `x` with
values in `[0, 1]`. These are the functions to which the analytic Beurling estimate is applied in
`BrownianBeurlingEstimateProof.lean`.
-/

set_option autoImplicit false

open MeasureTheory Set MarkovProcess
open _root_.HarmonicBalls
open scoped ENNReal

namespace MatedCRT.BrownianBeurling

/-- The paths that leave `O` no later than they hit `K`. -/
def avoidEvent (O K : Set ℂ) : Set (ContinuousPath ℂ) :=
  {ω | ContinuousPath.exitTime O ω ≤ ContinuousPath.exitTime Kᶜ ω}

/-- The probability that planar Brownian motion started at `x` leaves `O` no later than it hits `K`. -/
noncomputable def avoidanceProb (O K : Set ℂ) (x : ℂ) : ℝ :=
  (planarBrownianMotion x (avoidEvent O K)).toReal

theorem measurableSet_avoidEvent {O K : Set ℂ} (hO : IsOpen O) (hK : IsCompact K) :
    MeasurableSet (avoidEvent O K) :=
  Section6.measurableSet_avoid_before_exit hO hK

theorem measurable_avoidanceProb {O K : Set ℂ} (hO : IsOpen O) (hK : IsCompact K) :
    Measurable (avoidanceProb O K) :=
  (Section6.measurable_avoidance_probability hO hK).ennreal_toReal

theorem avoidanceProb_nonneg (O K : Set ℂ) (x : ℂ) : 0 ≤ avoidanceProb O K x :=
  ENNReal.toReal_nonneg

theorem avoidanceProb_le_one (O K : Set ℂ) (x : ℂ) : avoidanceProb O K x ≤ 1 := by
  unfold avoidanceProb
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

theorem ofReal_avoidanceProb (O K : Set ℂ) (x : ℂ) :
    ENNReal.ofReal (avoidanceProb O K x) = planarBrownianMotion x (avoidEvent O K) :=
  ENNReal.ofReal_toReal (measure_ne_top _ _)

end MatedCRT.BrownianBeurling
