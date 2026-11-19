import MatedCRT.FirstPass.Derived.LQGClockApproxAdapted
import LatticeProb.Prob.LimitAfterPositiveTimesAdapted

/-!
# The limiting LQG clock is adapted to the canonical filtration

The LQG clock along a path is the limit after positive times of the dyadic approximating clocks
`t ↦ ∫₀ᵗ ε^{γ²/2} e^{γ h_ε(b_s)} ds`, `ε = 2^{-j}`. Each approximating clock at time `t` depends only on
the path up to time `t`, so the limit clock at time `t` is measurable for the canonical filtration at
time `t`.
-/

namespace MatedCRT.LQGClockApproxAdapted

open MeasureTheory Set HarmonicBalls MarkovProcess
open scoped NNReal

/-- **Adaptedness of the limiting LQG clock.** If the circle averages at every dyadic scale are
measurable functions of the centre, then for every `t ≥ 0` the limit after positive times of the
dyadic approximating clocks, evaluated at time `t`, is measurable for the canonical filtration of
continuous planar paths at time `t`. -/
theorem measurable_limitAfterPositiveTimes_lqgClockApprox_canonicalFiltration (γ : ℝ)
    {hε : ℝ → ℂ → ℝ} (hmeas : ∀ j, Measurable (hε (HarmonicBalls.dyadicScale j))) (t : ℝ≥0) :
    Measurable[ContinuousPath.canonicalFiltration (alpha := ℂ) t] fun b : ContinuousPath ℂ =>
      LatticeProb.limitAfterPositiveTimes
        (fun j => lqgClockApprox γ hε (HarmonicBalls.dyadicScale j) b) t :=
  LatticeProb.measurable_limitAfterPositiveTimes_filtration
    (a := fun b j => lqgClockApprox γ hε (HarmonicBalls.dyadicScale j) b)
    ContinuousPath.canonicalFiltration
    (fun j v => measurable_lqgClockApprox_canonicalFiltration γ (hmeas j) v) t

end MatedCRT.LQGClockApproxAdapted
