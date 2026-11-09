import MatedCRT.Defs.Setting

/-!
# FIRST PASS frozen inputs of Lemma 5.3 (q3): the first-hit property of the space-filling SLE

Frozen by the operator ruling of 2026-11-09 20:12 UTC (item (b)): freeze the first-hit property as an EXTERNAL SLE input.
It is a property of the whole-plane space-filling SLE, not of this paper's clusters or harmonic balls.
-/

namespace MatedCRT

/-- **FIRST-PASS FROZEN.** First-hit property of the whole-plane space-filling SLE (operator ruling 2026-11-09 20:12 UTC, item
(b); checked TRUE, including the quantifier order a.s. omega then for all x, notes/fp-gaps/CHATGPT-frozen-truth-2145.md). For `0 < γ < 2` and a valid mated-CRT
environment `S`, almost surely, for every `x ∈ ℂ` the set of times `s` at which the curve `η` visits `x` is bounded below. This
makes the smallest vertex `a^ε_x = sInf {a | x ∈ H^ε_a}` of paper line 637 well defined (Defs/Map.lean `vertexOf`).
Source: Duplantier-Miller-Sheffield, arXiv:1409.7055v4, Lemma 8.11, p. 144. Used by: firstPass_5_3 via `mem_cell_vertexOf_of_first_hit` (FirstPass/S5c/CellFirstHit.lean),
which gives the hypothesis `hmemcell` of `core_subset_fillCells_eventually` (FirstPass/S5c/CoverEventually.lean). -/
def FPFirstHitVisits (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ᵐ ω ∂S.P, ∀ x : ℂ, BddBelow {s : ℝ | S.η ω s = x}

/-- **FIRST-PASS FROZEN.** Continuity of the disc Green function off its pole: for every `R > 0`, `G_{B_R}(0, ·)` is
continuous on `B_R \ {0}` (it is smooth there, with zero boundary values). Source: Harmonic-Balls-LQG Draft/Section2.lean
`GreenFunctionBallStmt`, Proposition 2.3 as cited by the paper; Armitage-Gardiner, Classical Potential Theory, §4.1.
Standard; locator pending. RETIRED (duplicate of FrozenGreenDiscPole, operator 22:43 UTC; no longer used). -/
def FPGreenBallContinuousOffPole : Prop :=
  ∀ R : ℝ, 0 < R →
    ContinuousOn (HarmonicBalls.greenFunction (Metric.ball (0 : ℂ) R) 0) (Metric.ball (0 : ℂ) R \ {0})

/-- **FIRST-PASS FROZEN.** Pole blow-up of the disc Green function: for every `R > 0`, `G_{B_R}(0, x) → +∞` as `x → 0`
with `x ≠ 0` (explicitly `G_{B_R}(0, x) = (2π)⁻¹ log (R / |x|)`). Source: Armitage-Gardiner, Classical Potential Theory,
§4.1 (the explicit Green function of a disc; Harmonic-Balls-LQG Defs/Green.lean `greenBall`). Standard; locator pending.
RETIRED (duplicate of FrozenGreenDiscPole, operator 22:43 UTC; no longer used). -/
def FPGreenBallPoleLimit : Prop :=
  ∀ R : ℝ, 0 < R →
    Filter.Tendsto (fun x : ℂ => HarmonicBalls.greenFunction (Metric.ball (0 : ℂ) R) 0 x)
      (nhdsWithin (0 : ℂ) {0}ᶜ) Filter.atTop

/-- **FIRST-PASS FROZEN.** Strong minimum principle for superharmonic functions (Armitage-Gardiner, Classical Potential
Theory, minimum principle: a superharmonic function on a connected open set attaining its infimum at an interior point is
constant). Distributional form: for an open connected `U ⊆ ℂ`, a function `f` continuous on `U` with `Δf ≤ 0` in `U` in
the sense of distributions (`HarmonicBalls.LaplacianLE f 0 U`; a continuous distributionally superharmonic function is
superharmonic), `f ≥ 0` on `U`, and `f x₀ = 0` at one point `x₀ ∈ U`, then `f = 0` on `U`. Standard; locator pending.
Used by: clusterMargin_pos_on_cluster (FirstPass/S5c/StrictComparison.lean; three-inputs A7). -/
def FPStrongMinimumPrinciple : Prop :=
  ∀ (U : Set ℂ) (f : ℂ → ℝ), IsOpen U → IsConnected U → ContinuousOn f U →
    HarmonicBalls.LaplacianLE f 0 U → (∀ x ∈ U, 0 ≤ f x) → ∀ x₀ ∈ U, f x₀ = 0 → ∀ x ∈ U, f x = 0

end MatedCRT
