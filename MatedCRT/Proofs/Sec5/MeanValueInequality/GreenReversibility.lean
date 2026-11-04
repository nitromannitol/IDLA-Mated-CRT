import MatedCRT.Proofs.Sec5.MeanValueInequality.Reversibility
import MatedCRT.Proofs.Sec4.ObstacleSpecialization.GreenMarkov

/-!
# Reversibility of the finite-volume killed Green function

Lyons and Peres, Exercise 2.1, obtained from the first-step equation and the
discrete divergence theorem.  The Green first-step infrastructure includes
work by Leonardo Bonanno.
-/

namespace MatedCRT

open Set

/-- The expected number of visits satisfies the detailed-balance identity on
a finite domain of a symmetric locally finite graph with consecutive edges. -/
theorem greenFn_reversible {m : ℤ → ℤ → ℕ} {A : Set ℤ}
    (hsymm : ∀ a b, m a b = m b a) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ a, m a (a + 1) ≠ 0) (hA : A.Finite) (a b : ℤ) :
    greenFn m A a b * (mdeg m a : ℝ) = greenFn m A b a * (mdeg m b : ℝ) :=
  greenFn_reversible_of_firstStep hsymm hlf hA
    (fun z => greenFn_laplacian_fst hlf hcons hA z) a b

end MatedCRT
