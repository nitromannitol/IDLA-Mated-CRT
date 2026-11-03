import MatedCRT.Defs.Setting
import MatedCRT.Defs.Sandpile

/-!
# Section 1: statements of Theorems 1.4 and 1.6 (lines 251-292)

Convergence of IDLA (Theorem 1.4) and of the divisible sandpile (Theorem 1.6) on the SLE/LQG embedding of the
`γ`-mated-CRT map to the `γ`-LQG harmonic balls of the `γ`-quantum cone.

## Conventions shared by all Draft files

* Every statement takes the space-filling SLE model `𝒮` (`MatedCRT.SpaceFillingSLEModel`, see
  `MatedCRT/Defs/Setting.lean`) and quantifies over `0 < γ < 2` and every environment `S : MatedCRTEnv Ω` which is
  valid for `𝒮` and `γ` (`S.IsValid 𝒮 γ`): the quantum cone `h`, `μ = μ_h`, the space-filling SLE_{16/γ²} `η`
  parametrized by `μ_h`-area, and the LQG clock.
* "The" family of harmonic balls `{Λ_t}` of Theorem 2.3 is any random family `Λ : Ω → ℝ → Set ℂ` which a.s. satisfies
  the conditions of Theorem 2.3 (`IsConeHarmonicBallFamily`); by the uniqueness in Theorem 2.3 it is a.s. the family
  of Theorem 2.3.
* The vertex `a = εk` of `𝒢^ε` is the integer `k`; the origin is `0`; cells are `cell ε (S.η ω) k`.
* IDLA walkers are, conditionally on `(h, η)`, independent simple random walks on `𝒢^ε` from the origin
  (`walkerSequenceLaw (S.mult ε ω) 0`); the annealed probability of an event is the `P`-integral of its conditional
  probability.
* Euclidean balls are `Metric.ball`; `B⁺_δ` and `B⁻_δ` are `outerNbhd δ` and `innerNbhd δ`.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- The approximation event of Theorem 1.4 for a set `X ⊆ ℂ` and `Λ ⊆ ℂ`: `B⁻_δ(Λ) ⊆ X ⊆ B⁺_δ(Λ)`. -/
def ApproximatesWithin (δ : ℝ) (Λ X : Set ℂ) : Prop :=
  innerNbhd δ Λ ⊆ X ∧ X ⊆ outerNbhd δ Λ

/-- **Theorem 1.4** (theorem:convergence-of-IDLA, line 251). Let `{Λ_t}` be the growing family of `γ`-LQG harmonic
balls of the `γ`-quantum cone with `μ_h(Λ_t) = t`. For each `δ > 0` and `t > 0`, with probability tending to `1` as
`ε → 0`, the union of the cells of the IDLA cluster after `⌊t ε⁻¹⌋` walkers satisfies
`B⁻_δ(Λ_t) ⊆ Ā_ε(⌊t ε⁻¹⌋) ⊆ B⁺_δ(Λ_t)`.
The probability is annealed: the conditional probability given `(h, η)` that the IDLA cluster fails the event,
integrated against `P`, tends to `0`. -/
def ConvergenceOfIDLAStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → 0 < t →
    Tendsto (fun ε => ∫⁻ ω, walkerSequenceLaw (S.mult ε ω) 0
        {xs | ¬ ApproximatesWithin δ (Λ ω t) (fillCells ε (S.η ω) (idlaCluster xs ⌊t / ε⌋₊))} ∂S.P)
      (𝓝[>] 0) (𝓝 0)

/-- **Theorem 1.6** (theorem:convergence-of-div-sandpile, line 283). Theorem 1.4 holds with the divisible sandpile
cluster `D̄_ε(t ε⁻¹)` started with mass `t ε⁻¹` at the origin in place of the IDLA cluster: for each `δ > 0` and
`t > 0`, with probability tending to `1` as `ε → 0`, `B⁻_δ(Λ_t) ⊆ D̄_ε(t ε⁻¹) ⊆ B⁺_δ(Λ_t)`. -/
def ConvergenceOfDivSandpileStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → 0 < t →
    ProbTendsToOne S.P fun ε =>
      {ω | ApproximatesWithin δ (Λ ω t) (fillCells ε (S.η ω) (sandpileCluster (S.mult ε ω) (t / ε)))}

end MatedCRT
