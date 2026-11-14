import MatedCRT.FirstPass.Derived.MedianOfCdf
import LatticeProb.Prob.PathSpaceScaling

/-!
# Time scaling and exit-time medians

The two continuous-path time-scaling maps agree, so a scale expressed using
LatticeProb's map can be recovered from exit-time medians.
-/

open MeasureTheory MarkovProcess
open scoped NNReal

namespace MatedCRT

variable {α : Type*} [MetricSpace α]

/-- The path-time scalings agree at every nonnegative scale. -/
theorem timeScalePath_eq_latticeProb (c : ℝ≥0) :
    (timeScalePath c : ContinuousPath α → ContinuousPath α) = LatticeProb.timeScalePath c := by
  funext f
  ext t
  rfl

/-- A scale in a path-law identity is recovered by the ratio of exit-time medians. -/
theorem coe_eq_medianOf_div_of_map_latticeProb_timeScalePath
    [MeasurableSpace α] [BorelSpace α] (U : Set α) (hU : IsOpen U)
    {c : ℝ≥0} (hc : c ≠ 0) (ν P₀ : Measure (ContinuousPath α))
    (hP₀ : P₀ = ν.map (LatticeProb.timeScalePath c))
    (hν : medianOf (exitCdf U ν) ≠ 0) :
    (c : ℝ) = medianOf (exitCdf U ν) / medianOf (exitCdf U P₀) := by
  apply coe_eq_medianOf_div_of_map_timeScalePath U hU hc ν P₀
  · simpa only [timeScalePath_eq_latticeProb] using hP₀
  · exact hν

end MatedCRT
