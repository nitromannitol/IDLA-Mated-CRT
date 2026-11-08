import Mathlib
import MatedCRT.Proofs.Probability.BrownianMaxCompat
import MatedCRT.Proofs.Sec1.EnvironmentScaling.BrownianSublinear

/-!
# Discharge of the named Step `GaussianBandStep` for Brownian motion with measurable coordinates

Component of `notes/env-steps/env-steps.tex:243-250`: the reflection bound for the maximum of the path
(`env-steps.tex:247-248`) and the sublinear growth `B t / t → 0` (the premise `hsub`).

`MatedCRT.Sec1.GaussianBandStep B P` is the Gaussian maximal estimate on a horizon. Here it is proved,
not assumed, for a Brownian motion `B` in the sense of Mathlib (`ProbabilityTheory.IsBrownianReal B P`)
on a probability space `(Ω, P)` whose coordinates `B t` are measurable. The proof is the ported
lattice-probability argument `MatedCRT.Probability.BrownianMaxCompat.measure_exists_abs_sub_ge_le`
(`MatedCRT/Proofs/Probability/BrownianMaxCompat.lean`; source `LatticeProb/Prob/BrownianMax.lean:247`,
commit 3912597a70dcc6c9b73042abd884a26989341c8d). The sublinear growth then follows from the existing
`MatedCRT.Sec1.ae_tendsto_div_real_of_gaussianBandStep` (BrownianSublinear.lean), unchanged.

The premises are explicit: the probability measure `[IsProbabilityMeasure P]` and the coordinate
measurability `hm : ∀ t, Measurable (B t)`. Nothing else is assumed.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace MatedCRT.Sec1

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The Gaussian maximal estimate, discharged.** For a Brownian motion `B` with measurable
coordinates on a probability space, the Step `GaussianBandStep B P` holds: for every horizon `T`
and every width `a > 0`, `P {∃ s ≤ T, a ≤ |B s - B 0|} ≤ 4 exp (-a ^ 2 / (32 T))`. -/
theorem gaussianBandStep_of_isBrownianReal {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : ProbabilityTheory.IsBrownianReal B P) (hm : ∀ t, Measurable (B t)) :
    GaussianBandStep B P := by
  unfold GaussianBandStep
  intro T a ha
  exact MatedCRT.Probability.BrownianMaxCompat.measure_exists_abs_sub_ge_le hB hm T ha

/-- **Real-time sublinear growth of Brownian motion, unconditional on the named Step.** For a
Brownian motion `B` with measurable coordinates on a probability space, almost surely
`B t / t → 0` as `t → ∞` through the reals, the path being read at `t.toNNReal`. This is
`ae_tendsto_div_real_of_gaussianBandStep` applied to `gaussianBandStep_of_isBrownianReal`. -/
theorem ae_tendsto_div_real_of_isBrownianReal {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : ProbabilityTheory.IsBrownianReal B P) (hm : ∀ t, Measurable (B t)) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℝ => B t.toNNReal ω / t) atTop (𝓝 0) :=
  ae_tendsto_div_real_of_gaussianBandStep (gaussianBandStep_of_isBrownianReal hB hm)

end MatedCRT.Sec1
