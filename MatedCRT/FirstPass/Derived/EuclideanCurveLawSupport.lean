import MatedCRT.FirstPass.Derived.EuclideanRaySupport
import LatticeProb.Topology.UnboundedRayCurveLaw

/-! # Unbounded support of Euclidean path laws -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set MarkovProcess HarmonicBalls ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.GMSMain
open LatticeProb.ReparamDistanceIsometry
open scoped ENNReal NNReal

/-- Reading complex paths in Euclidean coordinates is continuous. -/
theorem continuous_complexToEuclideanPath : Continuous complexToEuclideanPath :=
  ContinuousMap.continuous_postcomp _

/-- The Euclidean coordinate law of planar Brownian motion has unbounded range almost surely. -/
theorem ae_unbounded_range_map_planarBrownianMotion (y : ℂ) :
    ∀ᵐ (f : C(ℝ≥0, EuclideanSpace ℝ (Fin 2))) ∂((planarBrownianMotion y).map complexToEuclideanPath),
      ¬ Bornology.IsBounded (Set.range f) := by
  apply (ae_map_iff continuous_complexToEuclideanPath.measurable.aemeasurable
    (LatticeProb.measurableSet_continuousMap_unbounded_range (0 : EuclideanSpace ℝ (Fin 2)))).2
  exact ae_planarBrownianMotion_unbounded_euclidean_range y

/-- The Euclidean coordinate law of an embedded walk has unbounded range almost surely. -/
theorem ae_unbounded_range_map_integerWalk
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ))
    (hH : H.cell = cell ε η)
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj.Connected)
    (x : ℤ) {v : ℝ} (hv : 0 < v) :
    ∀ᵐ (f : C(ℝ≥0, EuclideanSpace ℝ (Fin 2))) ∂((srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x).map
        (fun ξ => complexToEuclideanPath (interpPathCM (vertexPoint ε η) hv.le ξ))),
      ¬ Bornology.IsBounded (Set.range f) := by
  have hm : Measurable (fun ξ => complexToEuclideanPath
      (interpPathCM (vertexPoint ε η) hv.le ξ)) :=
    continuous_complexToEuclideanPath.measurable.comp
      (measurable_interpPathCM (vertexPoint ε η) hv.le)
  apply (ae_map_iff hm.aemeasurable
    (LatticeProb.measurableSet_continuousMap_unbounded_range (0 : EuclideanSpace ℝ (Fin 2)))).2
  filter_upwards [ae_unbounded_euclidean_range_all_positive_speeds_integerWalk
    h hε m hlf H hH hconn x] with ξ hξ
  exact hξ v hv

end MatedCRT
end
