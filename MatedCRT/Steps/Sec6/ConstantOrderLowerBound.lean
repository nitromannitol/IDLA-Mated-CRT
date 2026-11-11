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

/-- **Lemma 6.7, route (b)** (lemma:constant-order-lower-bound, line 2410). The Draft statement `ConstantOrderLowerBoundStmt` with the absorption probability `s₂` replaced by
`s₂ / (1 + |log r|)²`: the proof (lines 2449-2461) passes the bound `1 - s₂ / (1 + |log r|)²` of Lemma 6.8 in its
route (b) form (`ConstantOrderLowerBoundDivLogStmt`) through unchanged. -/
def ConstantOrderLowerBoundLogStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ βm : ℝ, (2 + γ) ^ 2 / 2 < βm → ∃ ω₀ : ℝ, 0 < ω₀ ∧
  ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 → ∃ s₁ s₂ : ℝ, 0 < s₁ ∧ s₁ < 1 ∧ 0 < s₂ ∧ s₂ < 1 ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ dd : Ω → ℝ, Measurable[S.fieldSigma] dd ∧ (∀ ω, 0 < dd ω) ∧
    ProbTendsToOne S.P fun ε => {ω | ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ dd ω → ∀ Θ : Set ℤ,
      closure (fillCells ε (S.η ω) Θ) ⊆ ball 0 (ρ / 2) → ball 0 s₀ ⊆ fillCells ε (S.η ω) Θ →
      ∀ a ∈ vClosure (S.mult ε ω) Θ, ∀ S' ⊆ cellVertices ε (S.η ω) (thickening r (fillCells ε (S.η ω) Θ)),
        ((S' \ Θ).ncard : ℝ) < s₁ * r ^ (2 * βm) / ε →
        ENNReal.ofReal (s₂ / (1 + |Real.log r|) ^ 2) ≤ srwLaw (S.mult ε ω) a {x | ∃ n : ℕ,
          (n : ℕ∞) < vExitTime (cellVertices ε (S.η ω) (thickening r (fillCells ε (S.η ω) Θ))) x ∧
          x n ∈ cellVertices ε (S.η ω) (thickening r (fillCells ε (S.η ω) Θ)) \ (S' ∪ Θ)}}

/-- The drafted Lemma 6.7 implies its route (b) form (the probability only decreases). -/
theorem ConstantOrderLowerBoundStmt.logLoss {𝒮 : SpaceFillingSLEModel} (h : ConstantOrderLowerBoundStmt 𝒮) :
    ConstantOrderLowerBoundLogStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 βm hβm
  obtain ⟨ω₀, hω₀, h⟩ := h γ hγ hγ2 ρ hρ hρ1 βm hβm
  refine ⟨ω₀, hω₀, fun s₀ hs₀ hs₀1 => ?_⟩
  obtain ⟨s₁, s₂, hs₁, hs₁1, hs₂, hs₂1, h⟩ := h s₀ hs₀ hs₀1
  refine ⟨s₁, s₂, hs₁, hs₁1, hs₂, hs₂1, fun Ω _ S hS => ?_⟩
  obtain ⟨dd, hdd, hddpos, hE⟩ := h Ω S hS
  refine ⟨dd, hdd, hddpos, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hE (fun _ => zero_le)
    (fun ε => measure_mono (compl_subset_compl.2 fun ω hω => ?_))
  intro r hr1 hr2 Θ hΘ1 hΘ2 a ha S' hS' hcard
  have hL : 1 ≤ (1 + |Real.log r|) ^ 2 := one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg _))
  exact (ENNReal.ofReal_le_ofReal (div_le_self hs₂.le hL)).trans (hω r hr1 hr2 Θ hΘ1 hΘ2 a ha S' hS' hcard)

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
