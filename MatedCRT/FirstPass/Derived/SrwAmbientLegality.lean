import MatedCRT.FirstPass.S4S6c.FrontierSeparation
import MatedCRT.Proofs.Infra.RandomWalk

/-!
# Ambient graph legality of random walk

A walk whose edge multiplicities are supported on those of an ambient graph
follows ambient graph edges or stays in place.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace MatedCRT

/-- A walk supported on the ambient multiplicities starts at its prescribed
vertex and almost surely takes ambient graph edges or stays in place. -/
theorem srwLaw_ae_start_and_ambient_legal (m m' : ℤ → ℤ → ℕ) (a : ℤ)
    (hsupport : ∀ u v, m' u v ≠ 0 → m u v ≠ 0) :
    ∀ᵐ p ∂srwLaw m' a, p 0 = a ∧
      ∀ n, p (n + 1) = p n ∨ (adjGraph m).Adj (p n) (p (n + 1)) := by
  filter_upwards [srwLaw_ae_start m' a, FrontierSeparation.ae_srwStep_legal m' a] with p hstart hstep
  refine ⟨hstart, fun n => ?_⟩
  rcases hstep n with hstay | hedge
  · exact Or.inl hstay
  · by_cases heq : p (n + 1) = p n
    · exact Or.inl heq
    · right
      exact (SimpleGraph.fromRel_adj _ _ _).2
        ⟨Ne.symm heq, Or.inl (hsupport _ _ hedge)⟩

open Classical in
/-- The induced walk is almost surely legal in the ambient graph. -/
theorem srwLaw_induced_ae_start_and_ambient_legal (m : ℤ → ℤ → ℕ)
    (A : Set ℤ) (a : ℤ) :
    ∀ᵐ p ∂srwLaw (fun u v => if u ∈ A ∧ v ∈ A then m u v else 0) a,
      p 0 = a ∧ ∀ n, p (n + 1) = p n ∨ (adjGraph m).Adj (p n) (p (n + 1)) := by
  classical
  apply srwLaw_ae_start_and_ambient_legal
  intro u v h
  split_ifs at h with huv
  · exact h
  · exact (h rfl).elim

end MatedCRT
