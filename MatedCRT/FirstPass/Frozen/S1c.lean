import MatedCRT.Steps.Sec1.Convergence

/-!
# Frozen external inputs of the scaled cluster exit time

General facts used in the proof of the scaled cluster exit time: universal measurability of analytic sets, field-level measurability of the LQG measure against test functions, and the disc Green function with pole at the centre. The radial divergence of the conditioned Brownian motion is `FrozenConeRadialDivergenceCorrected` (`Frozen/S1cDivergence.lean`).
-/

namespace MatedCRT

open MeasureTheory Filter Topology HarmonicBalls MarkovProcess
open scoped NNReal

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
