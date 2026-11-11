import MatedCRT.Steps.Sec1.Convergence

/-!
# Frozen external input of the scaled cluster exit time

`FrozenConeRadialDivergence` is the one general Brownian fact used by the lower-tail bound for the cone scale radius `R_b` in the proof of the scaled cluster exit time. It concerns only the radial part of the quantum cone (the conditioned Brownian motion `B̂` of Definition 2.1 and its quantum cone radial law `quantumConeRadialLaw`), not harmonic balls, clusters or IDLA processes.
-/

namespace MatedCRT

open MeasureTheory Filter Topology HarmonicBalls MarkovProcess
open scoped NNReal

/-- Radial divergence of the conditioned process. For `0 < γ < 2` and every probability `ν` on continuous paths which is the conditioned Brownian motion `B̂` of `IsBMConditionedPositive (Q - γ) ν` (drift `c = Q - γ = 2/γ - γ/2 > 0`), `ν`-almost surely `B̂_s + c s → ∞` as `s → ∞` on `ℝ≥0`. In the coordinates of the quantum cone radial law (`quantumConeRadialLaw γ ν`, second component `s ↦ B̂_s - γ s`), this reads: almost surely the second path `x.2` satisfies `x.2 s + Q s → ∞`, with `Q = lqgQ γ`.
Source: the standard long-time behaviour of Brownian motion with positive drift conditioned to stay positive (Doob h-transform of drifted Brownian motion killed at `0`; `Y_s / s → c` a.s.), as used for the conditioned process of Duplantier-Miller-Sheffield (2014, *Mating of trees*, arXiv:1409.7055v4), Definition of the quantum cone; the identification of the weak limit `ν` of `IsBMConditionedPositive` with the h-transform is part of this standard fact. Locator: standard; locator not yet pinned.
Truth check: FALSE. The almost-sure conclusion lives on an uncountable raw function space with the product sigma-algebra, where real-time divergence is not an almost-sure property. Counterexample: the complement has outer measure one.
Retired and replaced by `FrozenConeRadialDivergenceCorrected`. -/
def FrozenConeRadialDivergence : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ν : Measure (ContinuousPath ℝ), IsBMConditionedPositive (lqgQ γ - γ) ν →
    ∀ᵐ x ∂(quantumConeRadialLaw γ ν),
      Tendsto (fun s : ℝ≥0 => x.2 s + lqgQ γ * (s : ℝ)) atTop atTop

/-- Universal measurability of analytic sets (Lusin). For every Polish space `X` with its Borel σ-algebra and every finite Borel measure `ν` on `X`, each analytic subset of `X` is `ν`-null-measurable (it is `ν`-measurable for the completion). Source: Lusin (1917); Kechris, *Classical Descriptive Set Theory* (1995), Theorem 21.10 (analytic sets are universally measurable). General measure theory, not specific to this paper. Locator: standard; locator not yet pinned.
Truth check: TRUE. Kechris (1995), Theorem 21.10, p. 155. -/
def FrozenUniversalMeasurabilityOfAnalytic : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X),
    IsFiniteMeasure ν → ∀ A : Set X, AnalyticSet A → NullMeasurableSet A ν

/-- Field-level measurability of the LQG measure against test functions. For `0 < γ < 2`, every γ-quantum cone field `(P, hC, hcirc, μ)` (`IsConeField`) and every continuous compactly supported `φ : ℂ → ℝ`, the map `ω ↦ ∫ φ dμ_ω` is almost everywhere measurable (`AEMeasurable _ P`, not `Measurable`: `IsLQGMeasure` constrains `μ` only almost surely, HB `Defs/LQG.lean:63`; a counterexample shows that everywhere measurability fails). This is the field-level measurability of the dyadic approximations of the LQG measure (Duplantier-Sheffield 2011, Prop. 1.1, as cited in `HarmonicBalls.Defs.LQG`), and the measurability of `ω ↦ μ_h(S)`, which determines it on dyadic squares. Locator: standard; locator not yet pinned.
Truth check: TRUE. DS arXiv:0808.1560v2 Proposition 1.1 (p. 5) and Proposition 3.1 (p. 17). -/
def FrozenLQGTestIntegralMeasurable : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
    ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ → AEMeasurable (fun ω => ∫ x, φ x ∂(μ ω)) P

/-- Disc Green function with pole at the centre. For every radius `R > 0`, the Green function `G_{B_R}(0,·) = greenFunction (ball 0 R) 0` is nonnegative and continuous on `B_R ∖ {0}`; explicitly `G_{B_R}(0,x) = (2π)^{-1} log (R / |x|)` (Armitage-Gardiner, *Classical Potential Theory* (2001), §4.4). This is the Green function of the disc, not specific to this paper. Locator: standard; locator not yet pinned.
Truth check: TRUE. Doob (1984), Ch. II §1, p. 14, equation (1.1), divided by 2π. -/
def FrozenDiskGreenNonnegCont : Prop :=
  ∀ R : ℝ, 0 < R → (∀ x ∈ Metric.ball (0 : ℂ) R, x ≠ 0 → 0 ≤ greenFunction (Metric.ball (0 : ℂ) R) 0 x) ∧
    ContinuousOn (greenFunction (Metric.ball (0 : ℂ) R) 0) (Metric.ball (0 : ℂ) R \ {0})

end MatedCRT
