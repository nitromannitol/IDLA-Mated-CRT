import MatedCRT.FirstPass.Derived.ExitPointTargetLaw
import MatedCRT.FirstPass.Derived.EuclideanRaySupport
import LatticeProb.Prob.ContinuousMapUnboundedRange

/-! # Unbounded paths under the anisotropic Brownian target -/

set_option autoImplicit false

open MeasureTheory Set MarkovProcess HarmonicBalls
open MatedCRT.TargetLawTemplateEvent MatedCRT.StopAtExitCmp
open ReflectedGMS.StatementIngredients

namespace MatedCRT

/-- An invertible linear image of a continuous path with unbounded range is unbounded. -/
theorem unbounded_range_matrixEquiv (L : ℂ ≃L[ℝ] ℂ) (b : ContinuousPath ℂ)
    (hb : ¬ Bornology.IsBounded (Set.range b)) :
    ¬ Bornology.IsBounded (Set.range ((⟨L, L.continuous⟩ : C(ℂ, ℂ)).comp b)) := by
  intro h
  apply hb
  have h' := (L.symm : ℂ →L[ℝ] ℂ).lipschitzWith.isBounded_image h
  change Bornology.IsBounded (L.symm '' Set.range ((⟨L, L.continuous⟩ : C(ℂ, ℂ)).comp b)) at h'
  have heq : L.symm '' Set.range ((⟨L, L.continuous⟩ : C(ℂ, ℂ)).comp b) = Set.range b := by
    ext z
    constructor
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, by simp⟩
    · rintro ⟨t, rfl⟩
      exact ⟨_, ⟨t, rfl⟩, by simp⟩
  rwa [heq] at h'

/-- The anisotropic Brownian target of the invariance principle has unbounded range almost surely. -/
theorem ae_unbounded_range_anisotropicBrownianTarget (target : AnisotropicBrownianTarget) :
    ∀ᵐ (f : BouRabeeGwynne.BrownianPath 2) ∂(target.pathLaw : Measure _),
      ¬ Bornology.IsBounded (Set.range f) := by
  rw [pathLaw_eq_map]
  apply (ae_map_iff ((measurable_linearImageBrownianPath _).comp
    measurable_complexPathToEuc).aemeasurable
    (LatticeProb.measurableSet_continuousMap_unbounded_range
      (0 : EuclideanSpace ℝ (Fin 2)))).2
  filter_upwards [ae_planarBrownianMotion_unbounded_range 0] with b hb
  change ¬ Bornology.IsBounded (Set.range (linearImageBrownianPath target.factor (complexPathToEuc b)))
  rw [linearImageBrownianPath_complexPathToEuc_eq (isUnit_det_factor target)]
  exact unbounded_range_complexToEuclideanPath _
    (unbounded_range_matrixEquiv (matrixEquiv (isUnit_det_factor target)) b hb)

end MatedCRT
