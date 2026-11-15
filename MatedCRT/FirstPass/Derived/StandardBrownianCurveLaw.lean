import MatedCRT.FirstPass.Derived.EuclideanCurveLawSupport
import MatedCRT.FirstPass.Derived.TargetLawTemplateEvent

/-! # Standard Brownian laws on local curve classes -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set HarmonicBalls
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayCurveSpace
open MatedCRT.TargetLawTemplateEvent
open scoped NNReal

local instance : IsProbabilityMeasure ((planarBrownianMotion 0).map complexToEuclideanPath) :=
  (Measure.isProbabilityMeasure_map_iff continuous_complexToEuclideanPath.measurable.aemeasurable).2 inferInstance

/-- Every standard Euclidean Brownian law is supported on unbounded rays. -/
theorem ae_unbounded_range_standardBrownianLaw
    {μ : Measure (BouRabeeGwynne.BrownianPath 2)}
    (hμ : BouRabeeGwynne.IsStandardBrownianLaw μ) :
    ∀ᵐ (f : BouRabeeGwynne.BrownianPath 2) ∂μ, ¬ Bornology.IsBounded (Set.range f) := by
  rw [eq_map_complexPathToEuc hμ]
  exact ae_unbounded_range_map_planarBrownianMotion 0

/-- The local curve law of standard Euclidean Brownian motion equals the law
obtained by reading planar Brownian motion in Euclidean coordinates. -/
theorem curveLaw_standardBrownian_eq_planar
    {μ : Measure (BouRabeeGwynne.BrownianPath 2)} [IsProbabilityMeasure μ]
    (hμ : BouRabeeGwynne.IsStandardBrownianLaw μ) :
    curveLaw μ (ae_unbounded_range_standardBrownianLaw hμ) =
      curveLaw ((planarBrownianMotion 0).map complexToEuclideanPath)
        (ae_unbounded_range_map_planarBrownianMotion 0) := by
  have h : μ = (planarBrownianMotion 0).map complexToEuclideanPath :=
    eq_map_complexPathToEuc hμ
  subst μ
  rfl

end MatedCRT
end
