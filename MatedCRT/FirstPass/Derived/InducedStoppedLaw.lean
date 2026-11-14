import MatedCRT.FirstPass.Derived.InducedStoppedLawCoupling
import LatticeProb.Walk.GraphBoundaryCoupling

/-!
# Induced walk stopped at the boundary

The induced and ambient walk have the same stopped interpolation law at the
inner boundary of the inducing vertex set.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal
open MatedCRT.ExitCouplingGlue

namespace MatedCRT

open Classical in
/-- An induced walk and the ambient walk started inside the inducing set have
    the same interpolated law when stopped on its inner boundary. -/
theorem induced_stoppedInterp_law_eq (m : ℤ → ℤ → ℕ) (A : Set ℤ)
    (a : ℤ) (ha : a ∈ A) (v : ℤ → ℂ) (speed : ℝ≥0) :
    (srwLaw (fun u w => if u ∈ A ∧ w ∈ A then m u w else 0) a).map
        (stoppedInterp v speed (LatticeProb.Graph.innerBoundary (adjGraph m) A)ᶜ) =
      (srwLaw m a).map
        (stoppedInterp v speed (LatticeProb.Graph.innerBoundary (adjGraph m) A)ᶜ) := by
  obtain ⟨P, Q, hP, hQ, hPlaw, hQlaw, hcouple⟩ :=
    LatticeProb.exists_productNoise_graphBoundary_trajectories (adjGraph m) A
      (srwKernel (fun u w => if u ∈ A ∧ w ∈ A then m u w else 0)) (srwKernel m)
      ((Set.to_countable _).measurableSet) (srwKernel_induced_eq_of_not_boundary m A) a
      (induced_or_ambient_trajMeasure_ae_legal m A a ha)
  exact induced_stoppedInterp_law_eq_of_trajectory_coupling _ m A a P Q hP hQ
    hPlaw hQlaw hcouple v speed

end MatedCRT
