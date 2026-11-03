import MatedCRT.Defs.Map
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.ConditionalProbability

/-!
# Simple random walk, discrete potential theory and IDLA on a multigraph on `ℤ`
(Sections 1.2.1, 2.7, 2.8 and 6, lines 245-249, 718-809, 2271-2287)

The vertices `a = εk` of the mated-CRT map are indexed by `k ∈ ℤ`. Given an edge multiplicity `m : ℤ → ℤ → ℕ`:

* `srwKernel m`: one step of *simple random walk*, which jumps along a uniformly chosen incident edge, i.e. to `b`
  with probability `m(a,b)/deg(a)` (a vertex with no or infinitely many edges, which does not occur for the
  mated-CRT map, is junk-absorbing);
* `srwLaw m a`: the law on paths `ℕ → ℤ` of simple random walk started from `a` (Ionescu-Tulcea, Mathlib's
  `Kernel.traj`);
* `vExitTime A x`: the first time `n ≥ 0` with `x n ∉ A` (`⊤` if none);
* the Green's function `G_A(a,b)` (expected number of visits to `b` before exiting `A`, eq:greens-function, line 752,
  with the overloaded notation of Remark 2.12 for a vertex set `A`), the Green's kernel `g_A(a,b) = G_A(a,b)/deg(b)`
  (eq:greens-kernel, line 757), the expected exit time `Q_A(a) = E[τ_A]` (eq:expected-exit-time, line 768) and the
  normalized expected exit time `q_A(a) = ∑_{b ∈ A} g_A(a,b)` (eq:normalized-exit-time, line 772).

"Conditionally on `(h, η)`" all of these are deterministic functions of the map; the paper's `E[· | h, η]` is the
expectation under `srwLaw`.

IDLA: `idlaAggregate Θ Θ' xs` is the aggregate `A(Θ; a₁, …, a_k → Θ')` of Definition 6.2 (line 2275) for walkers
with paths `xs = [x₁, …, x_k]` (`x_i 0 = a_i`), released one at a time in the order of the list: `Θ` is occupied, each
walker runs until it first leaves the current aggregate; if it is then inside `Θ'` it is absorbed (its position is
added), otherwise it is stopped outside `Θ'` and its position is recorded in `P(Θ; a₁, …, a_k → Θ')`, a list (with
multiplicity, in the order of the walkers; the printed "subset" of `∂Θ'`, line 2279, loses the multiplicity that the
restarted aggregate of Lemma 6.3 needs). With `Θ = ∅`, `Θ' = univ` and `n` walkers from the origin this is the IDLA
cluster `A_ε(n)` of line 246.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

/-- The measure `∑_b m(a,b) δ_b` on the neighbours of `a`, of total mass `deg(a)`. -/
noncomputable def edgeMeasure (m : ℤ → ℤ → ℕ) (a : ℤ) : Measure ℤ :=
  Measure.sum fun b => (m a b : ℝ≥0∞) • Measure.dirac b

open Classical in
/-- The one-step law of simple random walk from `a`: `edgeMeasure m a` normalized, i.e. `b ↦ m(a,b)/deg(a)`; the
Dirac mass at `a` if `a` has no edges or infinitely many (junk). -/
noncomputable def srwStep (m : ℤ → ℤ → ℕ) (a : ℤ) : Measure ℤ :=
  if edgeMeasure m a univ ≠ 0 ∧ edgeMeasure m a univ ≠ ⊤ then (edgeMeasure m a)[|univ] else Measure.dirac a

instance isProbabilityMeasure_srwStep (m : ℤ → ℤ → ℕ) (a : ℤ) : IsProbabilityMeasure (srwStep m a) := by
  unfold srwStep
  split_ifs with h
  · exact cond_isProbabilityMeasure_of_finite h.1 h.2
  · infer_instance

/-- The transition kernel of simple random walk on the multigraph `m`. -/
noncomputable def srwKernel (m : ℤ → ℤ → ℕ) : Kernel ℤ ℤ :=
  Kernel.ofFunOfCountable (srwStep m)

instance isMarkovKernel_srwKernel (m : ℤ → ℤ → ℕ) : IsMarkovKernel (srwKernel m) :=
  ⟨fun a => isProbabilityMeasure_srwStep m a⟩

/-- The step kernel from histories `(x₀, …, x_n)` to `x_{n+1}`, which only reads the current state `x_n`. -/
noncomputable def srwHistoryKernel (m : ℤ → ℤ → ℕ) (n : ℕ) : Kernel ((i : Finset.Iic n) → ℤ) ℤ :=
  (srwKernel m).comap (fun x => x ⟨n, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

instance isMarkovKernel_srwHistoryKernel (m : ℤ → ℤ → ℕ) (n : ℕ) :
    IsMarkovKernel (srwHistoryKernel m n) := by
  unfold srwHistoryKernel; infer_instance

/-- The law `P^a` on paths `ℕ → ℤ` of simple random walk on the multigraph `m` started from `a` (`x 0 = a`). -/
noncomputable def srwLaw (m : ℤ → ℤ → ℕ) (a : ℤ) : Measure (ℕ → ℤ) :=
  Kernel.traj (srwHistoryKernel m) 0 (fun _ => a)

instance isProbabilityMeasure_srwLaw (m : ℤ → ℤ → ℕ) (a : ℤ) : IsProbabilityMeasure (srwLaw m a) := by
  unfold srwLaw; infer_instance

open Classical in
/-- The first exit time `τ_A = inf {n ≥ 0 : x n ∉ A} ∈ ℕ ∪ {∞}` of a path from `A` (eq:exit-time, line 762). -/
noncomputable def vExitTime (A : Set ℤ) (x : ℕ → ℤ) : ℕ∞ :=
  if h : ∃ n, x n ∉ A then (Nat.find h : ℕ∞) else ⊤

open Classical in
/-- The first hitting time `inf {n ≥ 0 : x n ∈ B}` of `B`. -/
noncomputable def vHitTime (B : Set ℤ) (x : ℕ → ℤ) : ℕ∞ :=
  vExitTime Bᶜ x

/-- The number of times `n < τ_A` at which the path `x` is at `b` (the visits to `b` before exiting `A`). -/
noncomputable def visitsBeforeExit (A : Set ℤ) (b : ℤ) (x : ℕ → ℤ) : ℝ≥0∞ :=
  ∑' n : ℕ, (if (n : ℕ∞) < vExitTime A x ∧ x n = b then 1 else 0)

/-- The *Green's function* `G_A(a,b)`: the expected number of times simple random walk started at `a` hits `b` before
exiting `A` (eq:greens-function, line 752; Remark 2.12), as a real number (junk `0` if infinite). It vanishes when
`a ∉ A` or `b ∉ A`, as in the extension of line 760. -/
noncomputable def greenFn (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a b : ℤ) : ℝ :=
  (∫⁻ x, visitsBeforeExit A b x ∂srwLaw m a).toReal

/-- The *Green's kernel* `g_A(a,b) = G_A(a,b)/deg(b)` (eq:greens-kernel, line 757). -/
noncomputable def greenKernel (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a b : ℤ) : ℝ :=
  greenFn m A a b / (mdeg m b : ℝ)

/-- The *expected exit time* `Q_A(a) = E[τ_A]` of simple random walk started at `a` (eq:expected-exit-time,
line 768), in `[0, ∞]`. -/
noncomputable def expectedExitTime (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ) : ℝ≥0∞ :=
  ∫⁻ x, (vExitTime A x : ℝ≥0∞) ∂srwLaw m a

/-- The `N`-th moment `E[τ_A^N]` of the exit time (Lemma 2.18, line 919), in `[0, ∞]`. -/
noncomputable def exitTimeMoment (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ x, (vExitTime A x : ℝ≥0∞) ^ N ∂srwLaw m a

/-- The *normalized expected exit time* `q_A(a) = ∑_{b ∈ A} g_A(a,b)` (eq:normalized-exit-time, line 772). -/
noncomputable def normExitTime (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ) : ℝ :=
  ∑' b : A, greenKernel m A a b

/-! ## IDLA (Section 1.2.1 and Definition 6.2) -/

open Classical in
/-- The first site outside `A` visited by the path `x`, if any. -/
noncomputable def firstExitSite (A : Set ℤ) (x : ℕ → ℤ) : Option ℤ :=
  if h : ∃ n, x n ∉ A then some (x (Nat.find h)) else none

open Classical in
/-- One walker of the stopped IDLA process of Definition 6.2: from the state (aggregate `A`, stopped positions `p`),
the walker with path `x` runs until it first leaves `A`; it is absorbed there if that site lies in `Θ'`, and is
stopped (its position appended to `p`) otherwise. If it never leaves `A` the state is unchanged. -/
noncomputable def idlaStep (Θ' : Set ℤ) (s : Set ℤ × List ℤ) (x : ℕ → ℤ) : Set ℤ × List ℤ :=
  match firstExitSite s.1 x with
  | some b => if b ∈ Θ' then (s.1 ∪ {b}, s.2) else (s.1, s.2 ++ [b])
  | none => s

/-- The aggregate and stopped positions after releasing the walkers `xs` in order, starting from `Θ` occupied. -/
noncomputable def idlaRun (Θ Θ' : Set ℤ) (xs : List (ℕ → ℤ)) : Set ℤ × List ℤ :=
  xs.foldl (idlaStep Θ') (Θ, [])

/-- `A(Θ; a₁, …, a_k → Θ')` (Definition 6.2, line 2275) for walkers with paths `xs` (`x_i 0 = a_i`). -/
noncomputable def idlaAggregate (Θ Θ' : Set ℤ) (xs : List (ℕ → ℤ)) : Set ℤ :=
  (idlaRun Θ Θ' xs).1

/-- `P(Θ; a₁, …, a_k → Θ')` (Definition 6.2, line 2279): the positions, outside `Θ'`, of the walkers stopped before
being absorbed, in the order of the walkers. -/
noncomputable def idlaStopped (Θ Θ' : Set ℤ) (xs : List (ℕ → ℤ)) : List ℤ :=
  (idlaRun Θ Θ' xs).2

/-- The law of `k` independent simple random walks started at `a₁, …, a_k`. -/
noncomputable def walkersLaw (m : ℤ → ℤ → ℕ) {k : ℕ} (a : Fin k → ℤ) : Measure (Fin k → ℕ → ℤ) :=
  Measure.pi fun i => srwLaw m (a i)

/-- The law of the sequence of independent simple random walks, all started at `a`, released by IDLA. -/
noncomputable def walkerSequenceLaw (m : ℤ → ℤ → ℕ) (a : ℤ) : Measure (ℕ → ℕ → ℤ) :=
  Measure.infinitePi fun _ => srwLaw m a

/-- The IDLA cluster `A(n)` after `n` walkers with paths `xs 0, …, xs (n-1)` (line 246): `A(0) = ∅` and `A(n)` adds to
`A(n-1)` the first site outside `A(n-1)` visited by the `n`-th walker. Under `walkerSequenceLaw m 0` the walkers are
independent simple random walks from the origin. -/
noncomputable def idlaCluster (xs : ℕ → ℕ → ℤ) (n : ℕ) : Set ℤ :=
  idlaAggregate ∅ univ (List.ofFn fun i : Fin n => xs i)

/-- The IDLA cluster after `n` walkers, the walkers being stopped upon exiting `Θ'` (Proposition 5.1, line 1967;
Lemma 5.2, line 1989). -/
noncomputable def stoppedIDLACluster (Θ' : Set ℤ) (xs : ℕ → ℕ → ℤ) (n : ℕ) : Set ℤ :=
  idlaAggregate ∅ Θ' (List.ofFn fun i : Fin n => xs i)

end MatedCRT
