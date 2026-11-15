import MatedCRT.FirstPass.Derived.StandardBrownianCurveLaw
import MatedCRT.FirstPass.Derived.UniformStartStoppedBM

/-! # Coordinate law of planar Brownian motion at a starting point -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory HarmonicBalls
open LatticeProb.ReparamDistanceIsometry
open MatedCRT.TargetLawTemplateEvent MatedCRT.StopAtExitCmp
open scoped NNReal

/-- Translating a standard Euclidean Brownian path to a fixed point gives the
coordinate law of planar Brownian motion started at that point. -/
theorem map_standardBrownian_translate_eq_planar
    {μ : Measure (BouRabeeGwynne.BrownianPath 2)}
    (hμ : BouRabeeGwynne.IsStandardBrownianLaw μ) (z : ℂ) :
    μ.map (fun f => ContinuousMap.const ℝ≥0 (Complex.orthonormalBasisOneI.repr z) + f) =
      (planarBrownianMotion z).map complexToEuclideanPath := by
  have ht : Continuous (fun f : BouRabeeGwynne.BrownianPath 2 =>
      ContinuousMap.const ℝ≥0 (Complex.orthonormalBasisOneI.repr z) + f) :=
    continuous_const.add continuous_id
  rw [eq_map_complexPathToEuc hμ]
  change ((planarBrownianMotion 0).map complexToEuclideanPath).map _ = _
  rw [Measure.map_map ht.measurable
    continuous_complexToEuclideanPath.measurable,
    ← map_translatePath_planarBrownianMotion z,
    Measure.map_map continuous_complexToEuclideanPath.measurable (translatePath z).measurable]
  congr 1
  funext f
  apply ContinuousMap.ext
  intro t
  change Complex.orthonormalBasisOneI.repr z +
      Complex.orthonormalBasisOneI.repr (f t) =
    Complex.orthonormalBasisOneI.repr (f t + z)
  rw [map_add, add_comm]

end MatedCRT
end
