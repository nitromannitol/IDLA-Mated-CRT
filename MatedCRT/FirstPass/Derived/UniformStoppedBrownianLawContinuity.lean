import MatedCRT.FirstPass.Derived.JointBallStoppedBrownianLawContinuity
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.UniformSpace.HeineCantor
import MarkovProcess.Path.Polish

/-! # Uniform continuity of stopped Brownian laws -/

set_option autoImplicit false

open MeasureTheory MarkovProcess

namespace MatedCRT.StopAtExitCmp

noncomputable local instance : PseudoMetricSpace (ContinuousPath ℂ) :=
  TopologicalSpace.pseudoMetrizableSpacePseudoMetric (ContinuousPath ℂ)

/-- On a compact set of starts and radii, stopped planar Brownian laws vary
uniformly in the Lévy–Prokhorov distance for the chosen compatible path metric. -/
theorem uniform_stoppedBrownianLaw_levyProkhorovDist
    (K : Set (ℂ × ℝ)) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ p ∈ K, ∀ q ∈ K, dist p q < δ →
      levyProkhorovDist (planarBrownianStoppedBallLaw p.1 p.2 :
        Measure (ContinuousPath ℂ)) (planarBrownianStoppedBallLaw q.1 q.2 :
        Measure (ContinuousPath ℂ)) < ε := by
  have hcont : Continuous (fun p : ℂ × ℝ =>
      LevyProkhorov.ofMeasure (planarBrownianStoppedBallLaw p.1 p.2)) :=
    LevyProkhorov.continuous_ofMeasure_probabilityMeasure.comp
      continuous_planarBrownianStoppedBallLaw
  have huc := hK.uniformContinuousOn_of_continuous hcont.continuousOn
  obtain ⟨δ, hδ, hδprop⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  refine ⟨δ, hδ, ?_⟩
  intro p hp q hq hpq
  simpa only [LevyProkhorov.dist_probabilityMeasure_def] using hδprop p hp q hq hpq

end MatedCRT.StopAtExitCmp
