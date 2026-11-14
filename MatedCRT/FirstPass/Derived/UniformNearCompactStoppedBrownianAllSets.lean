import MatedCRT.FirstPass.Derived.UniformNearCompactStoppedBrownianLawContinuity
import LatticeProb.Prob.LevyProkhorovAllSets

/-! # Uniform bounds for stopped Brownian laws on arbitrary sets -/

set_option autoImplicit false

open MeasureTheory MarkovProcess

namespace MatedCRT.StopAtExitCmp

noncomputable local instance : PseudoMetricSpace (ContinuousPath ℂ) :=
  TopologicalSpace.pseudoMetrizableSpacePseudoMetric (ContinuousPath ℂ)

/-- Near a compact set of starts and radii, the stopped Brownian laws satisfy
uniform Lévy–Prokhorov bounds for every set of paths, using the chosen compatible
path pseudometric. -/
theorem uniform_near_compact_stoppedBrownianLaw_measure_le_thickening
    (K : Set (ℂ × ℝ)) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ p ∈ K, ∀ q : ℂ × ℝ, dist p q < δ →
      ∀ A : Set (ContinuousPath ℂ),
        (planarBrownianStoppedBallLaw p.1 p.2 : Measure (ContinuousPath ℂ)) A ≤
          (planarBrownianStoppedBallLaw q.1 q.2 : Measure (ContinuousPath ℂ))
            (Metric.thickening ε A) + ENNReal.ofReal ε := by
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨δ, hδ, hδprop⟩ :=
    uniform_near_compact_stoppedBrownianLaw_levyProkhorovDist K hK (ε / 2) hhalf
  refine ⟨δ, hδ, ?_⟩
  intro p hp q hpq A
  let μ : Measure (ContinuousPath ℂ) := planarBrownianStoppedBallLaw p.1 p.2
  let ν : Measure (ContinuousPath ℂ) := planarBrownianStoppedBallLaw q.1 q.2
  have hd : levyProkhorovEDist μ ν < ENNReal.ofReal (ε / 2) := by
    rw [← ENNReal.ofReal_toReal (levyProkhorovEDist_ne_top μ ν)]
    exact (ENNReal.ofReal_lt_ofReal_iff hhalf).2 (hδprop p hp q hpq)
  have hbound := LatticeProb.measure_le_thickening_of_levyProkhorovEDist_lt
    μ ν hhalf hhalf hd A
  have hadd : ε / 2 + ε / 2 = ε := add_halves ε
  rw [hadd] at hbound
  exact hbound.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal (half_le_self hε.le)))

end MatedCRT.StopAtExitCmp
