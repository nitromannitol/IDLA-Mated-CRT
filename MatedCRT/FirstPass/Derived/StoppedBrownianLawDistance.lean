import MatedCRT.FirstPass.Derived.JointBallStoppedBrownianProbability
import LatticeProb.Prob.ProbabilityMeasureDistance
import MarkovProcess.Path.Polish

/-! # Measurability of stopped Brownian law distances -/

set_option autoImplicit false

open MeasureTheory MarkovProcess

namespace MatedCRT.StopAtExitCmp

noncomputable local instance : PseudoMetricSpace (ContinuousPath ℂ) :=
  TopologicalSpace.pseudoMetrizableSpacePseudoMetric (ContinuousPath ℂ)

/-- The Lévy–Prokhorov distance to a stopped planar Brownian law is measurable in
its start, ball radius, and the other probability law. The path metric is the
compatible metric chosen by `pseudoMetrizableSpacePseudoMetric`. -/
theorem measurable_stoppedBrownianLaw_levyProkhorovDist :
    Measurable (fun p : (ℂ × ℝ) × ProbabilityMeasure (ContinuousPath ℂ) =>
      levyProkhorovDist (planarBrownianStoppedBallLaw p.1.1 p.1.2 :
        Measure (ContinuousPath ℂ)) (p.2 : Measure (ContinuousPath ℂ))) := by
  exact LatticeProb.measurable_levyProkhorovDist
    (measurable_planarBrownianStoppedBallLaw.comp measurable_fst) measurable_snd

end MatedCRT.StopAtExitCmp
