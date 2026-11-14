import MatedCRT.FirstPass.Derived.EuclideanBrownianExitPointLaw
import MatedCRT.FirstPass.Derived.BrownianDiscPoissonExit

/-! # Brownian disc exit laws in Euclidean coordinates -/

set_option autoImplicit false

open MeasureTheory Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

/-- The complex exit-point law from an interior point is disc harmonic measure. -/
theorem planarBrownianBallExitPointLaw_eq_discHarmonicMeasure
    {x : ℂ} {r : ℝ} (hx : x ∈ ball (0 : ℂ) r) :
    (planarBrownianBallExitPointLaw x r : Measure ℂ) = discHarmonicMeasure 0 r x := by
  have hm : Measurable (planarBallPathClock r) :=
    measurable_planarBallPathClock.comp (measurable_id.prodMk measurable_const)
  change ((planarBrownianMotion x).map (planarBallPathClock r)).map pathClockPoint = _
  rw [Measure.map_map measurable_pathClockPoint hm]
  exact planarBrownian_disc_exit_distribution_of_mem hx

/-- The Euclidean exit-point law is the coordinate image of disc harmonic measure. -/
theorem euclideanBrownianBallExitPointLaw_eq_discHarmonicMeasure_map
    {x : ℂ} {r : ℝ} (hx : x ∈ ball (0 : ℂ) r) :
    (euclideanBrownianBallExitPointLaw x r : Measure (EuclideanSpace ℝ (Fin 2))) =
      (discHarmonicMeasure 0 r x).map Complex.orthonormalBasisOneI.repr := by
  rw [euclideanBrownianBallExitPointLaw_eq_map]
  change (planarBrownianBallExitPointLaw x r : Measure ℂ).map _ = _
  rw [planarBrownianBallExitPointLaw_eq_discHarmonicMeasure hx]

end MatedCRT.StopAtExitCmp
