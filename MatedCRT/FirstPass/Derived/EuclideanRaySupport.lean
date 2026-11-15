import MatedCRT.FirstPass.Derived.IntegerWalkUnboundedRange
import MatedCRT.FirstPass.Derived.InterpolatedWalkPath
import MatedCRT.FirstPass.Derived.PlanarBrownianUnboundedRange
import LatticeProb.Topology.ReparamDistanceIsometry

/-! # Unbounded Euclidean coordinates of embedded paths -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set MarkovProcess HarmonicBalls ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.GMSMain
open LatticeProb.ReparamDistanceIsometry
open scoped ENNReal NNReal

/-- The standard Euclidean coordinates preserve unbounded path ranges. -/
theorem unbounded_range_complexToEuclideanPath (f : ContinuousPath ℂ)
    (hf : ¬ Bornology.IsBounded (Set.range f)) :
    ¬ Bornology.IsBounded (Set.range (complexToEuclideanPath f)) := by
  intro h
  apply hf
  have hi := Complex.orthonormalBasisOneI.repr.symm.isometry.lipschitzWith.isBounded_image h
  have heq : Complex.orthonormalBasisOneI.repr.symm ''
      Set.range (complexToEuclideanPath f) = Set.range f := by
    ext z
    constructor
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, by simp [complexToEuclideanPath]⟩
    · rintro ⟨t, rfl⟩
      exact ⟨_, ⟨t, rfl⟩, by simp [complexToEuclideanPath]⟩
  rwa [heq] at hi

/-- The embedded walk has unbounded Euclidean range at every positive speed almost surely. -/
theorem ae_unbounded_euclidean_range_all_positive_speeds_integerWalk
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ))
    (hH : H.cell = cell ε η)
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj.Connected)
    (x : ℤ) :
    ∀ᵐ ξ ∂srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x,
      ∀ (v : ℝ) (hv : 0 < v), ¬ Bornology.IsBounded
        (Set.range (complexToEuclideanPath (interpPathCM (vertexPoint ε η) hv.le ξ))) := by
  filter_upwards [ae_unbounded_range_all_positive_speeds_integerWalk h hε m hlf H hH hconn x]
    with ξ hξ
  intro v hv
  apply unbounded_range_complexToEuclideanPath
  have heq : (⇑(interpPathCM (vertexPoint ε η) hv.le ξ)) =
      interpolatedWalk ε η v ξ := funext (interpPathCM_vertexPoint ε η hv.le ξ)
  rw [heq]
  exact hξ v hv

/-- Planar Brownian motion has unbounded Euclidean range almost surely. -/
theorem ae_planarBrownianMotion_unbounded_euclidean_range (y : ℂ) :
    ∀ᵐ b ∂planarBrownianMotion y,
      ¬ Bornology.IsBounded (Set.range (complexToEuclideanPath b)) := by
  filter_upwards [ae_planarBrownianMotion_unbounded_range y] with b hb
  exact unbounded_range_complexToEuclideanPath b hb

end MatedCRT
end
