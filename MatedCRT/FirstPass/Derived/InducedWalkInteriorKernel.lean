import MatedCRT.FirstPass.Derived.InducedWalkKernel
import MatedCRT.Defs.Map
import LatticeProb.Graph.Boundary

/-!
# Induced walk transitions away from the boundary

An induced multigraph and its ambient graph have the same walk transition at
vertices in the interior of the inducing set.
-/

set_option autoImplicit false

open Set

namespace MatedCRT

open Classical in
/-- The induced and ambient kernels agree outside the complement and inner boundary. -/
theorem srwKernel_induced_eq_of_not_boundary (m : ℤ → ℤ → ℕ)
    (A : Set ℤ) (x : ℤ)
    (hx : x ∉ Aᶜ ∪ LatticeProb.Graph.innerBoundary (adjGraph m) A) :
    srwKernel (fun u v => if u ∈ A ∧ v ∈ A then m u v else 0) x = srwKernel m x := by
  classical
  have hxA : x ∈ A := by
    by_contra h
    exact hx (Or.inl h)
  apply srwKernel_induced_eq m A x hxA
  intro y hy
  by_contra hxy
  have hne : x ≠ y := by
    intro h
    subst y
    exact hy hxA
  apply hx
  right
  refine ⟨hxA, y, hy, ?_⟩
  exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, Or.inl hxy⟩

end MatedCRT
