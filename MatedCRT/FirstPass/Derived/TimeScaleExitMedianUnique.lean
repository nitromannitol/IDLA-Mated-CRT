import MatedCRT.FirstPass.Derived.TimeScalePathBridge

/-!
# Uniqueness of time scaling from exit medians

A nonzero exit median determines the time scale of a continuous-path law.
-/

open MeasureTheory MarkovProcess
open scoped NNReal

namespace MatedCRT

/-- A path law with a nonzero exit median has at most one nonzero time scale
leading to a given image law. -/
theorem timeScalePath_eq_of_map_eq
    {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
    (U : Set α) (hU : IsOpen U) {c d : ℝ≥0} (hc : c ≠ 0) (hd : d ≠ 0)
    (ν : Measure (ContinuousPath α)) (hν : medianOf (exitCdf U ν) ≠ 0)
    (h : ν.map (LatticeProb.timeScalePath c) = ν.map (LatticeProb.timeScalePath d)) :
    c = d := by
  apply NNReal.coe_injective
  calc
    (c : ℝ) = medianOf (exitCdf U ν) /
        medianOf (exitCdf U (ν.map (LatticeProb.timeScalePath d))) :=
      coe_eq_medianOf_div_of_map_latticeProb_timeScalePath U hU hc ν _ h.symm hν
    _ = (d : ℝ) :=
      (coe_eq_medianOf_div_of_map_latticeProb_timeScalePath U hU hd ν _ rfl hν).symm

/-- Equal nonzero exit medians force the time scale of the image law to be one. -/
theorem timeScalePath_eq_one_of_median_eq
    {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
    (U : Set α) (hU : IsOpen U) {c : ℝ≥0} (hc : c ≠ 0)
    (ν : Measure (ContinuousPath α)) (hν : medianOf (exitCdf U ν) ≠ 0)
    (h : medianOf (exitCdf U (ν.map (LatticeProb.timeScalePath c))) =
      medianOf (exitCdf U ν)) : c = 1 := by
  apply NNReal.coe_injective
  have hscale := coe_eq_medianOf_div_of_map_latticeProb_timeScalePath U hU hc ν _ rfl hν
  rw [h, div_self hν] at hscale
  exact hscale

end MatedCRT
