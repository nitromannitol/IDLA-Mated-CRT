import MatedCRT.Draft.Section6

/-!
# Lemma 6.7 (lemma:constant-order-lower-bound, line 2410): carving of the proof assuming Lemma 6.8 (lines 2449-2461)

The printed proof: by the strong Markov property (and Lemma 2.8), the trace of a walk started at `a ∈ cl(Θ)` contains
the trace of a walk started at some `b ∈ V^ε(∂(Θ̄ + B_{r/2}))`; with `A := S \ Θ`, Lemma 6.8 bounds by `1 - s₂` the
probability that the latter walk exits `V^ε(Θ̄ + B_r) \ Θ` through `A`, i.e. that the former never visits
`V^ε(Θ̄ + B_r) \ (S ∪ Θ)` before exiting `V^ε(Θ̄ + B_r)`.

The first sentence uses three facts which the printed proof leaves implicit:
* the walk does exit `V^ε(Θ̄ + B_r)` (more precisely `V^ε(Θ̄ + B_{r/2}) \ V^ε(∂(Θ̄ + B_{r/2}))`), almost surely given
  `(h, η)`: `WalkExitsStep`, from Lemma 2.19 (`Q^ε_D < ∞`);
* before exiting it visits `V^ε(∂(Θ̄ + B_{r/2}))`: deterministic, since the cells are connected, the cells of adjacent
  vertices intersect, and the walk only moves along edges (`SrwAeAdjacentStep`);
* the strong Markov property at the hitting time of `V^ε(∂(Θ̄ + B_{r/2}))`: `SrwHitDecompositionStep`.
The deduction "`|S \ Θ| < s₁ r^{2β⁻} ε⁻¹` implies `|A ∩ V^ε(B_r(z))| < s₁ r^{2β⁻} ε⁻¹`" (line 2453) needs `S \ Θ`
finite (`Set.ncard` of an infinite set is `0`; for `U \ Θ` infinite and `S = U` the conclusion of Lemma 6.7 would
fail): `CellVerticesBallFiniteStep`, `V^ε(B_ρ)` is finite.

The general walk facts (`SrwHitDecompositionStep`, `SrwAeAdjacentStep`) are stated for every multigraph on `ℤ`.
The reduction `constantOrderLowerBound_of_steps` is in MatedCRT/Proofs/Sec6/ConstantOrderLowerBound/OfSteps.lean.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

/-- Step (strong Markov property of simple random walk at the hitting time of `B`, any multigraph `m` on `ℤ`): if
the walk started at each `b ∈ B` lies in the measurable path event `F` with probability at most `c`, then the walk
started at `a` hits `B` and, from its hitting position on, lies in `F` with probability at most `c`. -/
def SrwHitDecompositionStep : Prop :=
  ∀ (m : ℤ → ℤ → ℕ) (a : ℤ) (B : Set ℤ) (F : Set (ℕ → ℤ)) (c : ℝ≥0∞), MeasurableSet F →
    (∀ b ∈ B, srwLaw m b F ≤ c) →
    srwLaw m a {x | ∃ n : ℕ, x n ∈ B ∧ (∀ j < n, x j ∉ B) ∧ (fun i => x (n + i)) ∈ F} ≤ c

/-- Step (simple random walk moves along edges, any multigraph `m` on `ℤ`): almost surely each step of the walk is
either along an edge or (junk, at a vertex of degree `0` or `∞`) a stay. -/
def SrwAeAdjacentStep : Prop :=
  ∀ (m : ℤ → ℤ → ℕ) (a : ℤ), ∀ᵐ x ∂srwLaw m a, ∀ n : ℕ, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0

/-- Step (`V^ε(B_ρ)` is finite, with probability tending to `1`): the cells which meet `B_ρ` are finitely many
(from Lemma 2.8, the area parametrization of `η` and `μ_h(B_1) < ∞`: each cell has `μ_h`-mass `ε`, and distinct cells
overlap in `μ_h`-null sets). -/
def CellVerticesBallFiniteStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ProbTendsToOne S.P fun ε => {ω | (cellVertices ε (S.η ω) (ball 0 ρ)).Finite}

/-- Step (the walk exits, with probability tending to `1`): for every open `O` with `B_{s₀} ⊆ O ⊆ B_ρ`, simple random
walk on `𝒢^ε` started anywhere a.s. exits `V^ε(O) \ V^ε(∂O)` (from Lemma 2.19, `Q^ε_O < ∞` once `μ_h(O) ≥ ε^α`). -/
def WalkExitsStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ s₀ : ℝ, 0 < ρ → ρ < 1 → 0 < s₀ →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ProbTendsToOne S.P fun ε => {ω | ∀ O : Set ℂ, IsOpen O → ball 0 s₀ ⊆ O → O ⊆ ball 0 ρ → ∀ a : ℤ,
      srwLaw (S.mult ε ω) a {x | vExitTime (interiorCellVertices ε (S.η ω) O) x = ⊤} = 0}

end MatedCRT
