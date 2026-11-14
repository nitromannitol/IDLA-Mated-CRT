import MatedCRT.FirstPass.Derived.UniformStoppedBrownianLawContinuity
import Mathlib.Topology.MetricSpace.Thickening

/-! # Uniform continuity of stopped Brownian laws near compact sets -/

set_option autoImplicit false

open MeasureTheory MarkovProcess

namespace MatedCRT.StopAtExitCmp

noncomputable local instance : PseudoMetricSpace (ContinuousPath ℂ) :=
  TopologicalSpace.pseudoMetrizableSpacePseudoMetric (ContinuousPath ℂ)

/-- Stopped planar Brownian laws vary uniformly near a compact set of starts
and radii, in the Lévy–Prokhorov distance for the chosen compatible path metric. -/
theorem uniform_near_compact_stoppedBrownianLaw_levyProkhorovDist
    (K : Set (ℂ × ℝ)) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ p ∈ K, ∀ q : ℂ × ℝ, dist p q < δ →
      levyProkhorovDist (planarBrownianStoppedBallLaw p.1 p.2 :
        Measure (ContinuousPath ℂ)) (planarBrownianStoppedBallLaw q.1 q.2 :
        Measure (ContinuousPath ℂ)) < ε := by
  have hC : IsCompact (Metric.cthickening 1 K) := hK.cthickening
  obtain ⟨δ, hδ, hδprop⟩ :=
    uniform_stoppedBrownianLaw_levyProkhorovDist (Metric.cthickening 1 K) hC ε hε
  refine ⟨min δ 1, lt_min hδ zero_lt_one, ?_⟩
  intro p hp q hpq
  have hpC : p ∈ Metric.cthickening 1 K := Metric.self_subset_cthickening K hp
  have hqC : q ∈ Metric.cthickening 1 K :=
    Metric.mem_cthickening_of_dist_le q p 1 K hp
      (le_of_lt (by simpa only [dist_comm] using lt_of_lt_of_le hpq (min_le_right δ 1)))
  exact hδprop p hpC q hqC (lt_of_lt_of_le hpq (min_le_left δ 1))

end MatedCRT.StopAtExitCmp
