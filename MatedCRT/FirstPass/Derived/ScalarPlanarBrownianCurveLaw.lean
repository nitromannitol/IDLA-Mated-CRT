import MatedCRT.FirstPass.Derived.StandardBrownianCurveLaw
import LatticeProb.Topology.StandardBrownianCurveSupport

/-! # Scalar Brownian motion on local curve classes -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set HarmonicBalls
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayCurveSpace
open LatticeProb.UnboundedRayIntervalIntegrand
open scoped NNReal

local instance : IsProbabilityMeasure ((planarBrownianMotion 0).map complexToEuclideanPath) :=
  (Measure.isProbabilityMeasure_map_iff continuous_complexToEuclideanPath.measurable.aemeasurable).2 inferInstance

/-- A positive scalar Brownian target and planar Brownian motion from zero have
identical local curve laws in Euclidean coordinates. -/
theorem curveLaw_scalarBrownian_eq_planar
    (target : ReflectedGMS.StatementIngredients.AnisotropicBrownianTarget)
    {s : ℝ≥0} (hs : 0 < s) (hfac : target.factor = (s : ℝ) • 1) :
    ∃ hν : ∀ᵐ (f : Path 2) ∂(target.pathLaw : Measure (Path 2)),
      ¬ Bornology.IsBounded (Set.range f),
      curveLaw (target.pathLaw : Measure (Path 2)) hν =
        curveLaw ((planarBrownianMotion 0).map complexToEuclideanPath)
          (ae_unbounded_range_map_planarBrownianMotion 0) := by
  obtain ⟨hν, hcurve⟩ := curveLaw_scalarBrownian_of_positive target hs hfac
  refine ⟨hν, ?_⟩
  exact hcurve.trans (curveLaw_standardBrownian_eq_planar target.isStandard)

end MatedCRT
end
