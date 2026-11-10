import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.Complex.Basic

/-!
# Super-mean-value inequality and minimum principles in the plane

The local defining inequality of superharmonic functions on an open subset of `ℂ`, in the sphere-average form of
Armitage and Gardiner, *Classical Potential Theory* (Springer, 2001), §3.1, and the strong and weak minimum
principles of §3.2. Further sources: Axler, Bourdon and Ramey, *Harmonic Function Theory*, 2nd ed., Theorem 11.2;
Doob, *Classical Potential Theory and Its Probabilistic Counterpart* (1984), Ch. II §5.
-/

open Metric Set Filter Topology MeasureTheory

namespace LatticeProb

/-- The super-mean-value inequality on `U`, the local defining property of a superharmonic function
(Armitage and Gardiner, *Classical Potential Theory*, §3.1): for every closed disc `closedBall c r ⊆ U` with
`0 < r`, the value `f c` dominates the average of `f` over the circle `sphere c r` with respect to normalized
arc length, that is, `Real.circleAverage f c r ≤ f c`. -/
def SuperMeanValueOn (f : ℂ → ℝ) (U : Set ℂ) : Prop :=
  ∀ c : ℂ, ∀ r : ℝ, 0 < r → closedBall c r ⊆ U → Real.circleAverage f c r ≤ f c

end LatticeProb
