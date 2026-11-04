import MatedCRT.Defs.RandomWalk

/-!
# Hitting probabilities and visit counts of the IDLA walkers (Lemma 5.2, lines 2162-2168)

On a fixed multigraph `m`, for a vertex set `O` and a site `a`:
* `hitBeforeExitProb m O a z = P^z[τ_a < T_O]`;
* `visitCount O a xs n` (the paper's `M`): the number of the first `n` walkers which hit `a` before exiting `O`;
* `lateVisitCount C O a xs n` (the paper's `L`): those which moreover leave the cluster `C i` of the previous walkers
  before hitting `a`.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set

/-- `P^z[τ_a < T_O]`: the probability that simple random walk on `m` started at `z` hits `a` before exiting `O`
(eq:markov-chain-renewal, line 2176). -/
noncomputable def hitBeforeExitProb (m : ℤ → ℤ → ℕ) (O : Set ℤ) (a z : ℤ) : ℝ :=
  (srwLaw m z {x | vHitTime {a} x < vExitTime O x}).toReal

open Classical in
/-- `M`: the number of the first `n` walkers `xs 0, …, xs (n-1)` which hit `a` before exiting `O` (line 2165). -/
noncomputable def visitCount (O : Set ℤ) (a : ℤ) (xs : ℕ → ℕ → ℤ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun i => vHitTime {a} (xs i) < vExitTime O (xs i)).card

open Classical in
/-- `L`: the number of the first `n` walkers which hit `a` before exiting `O`, but not before exiting the cluster
`C i` left by the previous walkers (`σ^i ≤ τ^i_a < T^i`, line 2167). -/
noncomputable def lateVisitCount (C : ℕ → Set ℤ) (O : Set ℤ) (a : ℤ) (xs : ℕ → ℕ → ℤ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun i =>
    vExitTime (C i) (xs i) ≤ vHitTime {a} (xs i) ∧ vHitTime {a} (xs i) < vExitTime O (xs i)).card

instance isProbabilityMeasure_walkerSequenceLaw (m : ℤ → ℤ → ℕ) (a : ℤ) :
    IsProbabilityMeasure (walkerSequenceLaw m a) := by
  unfold walkerSequenceLaw; infer_instance

end MatedCRT
