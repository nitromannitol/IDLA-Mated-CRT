import MatedCRT.FirstPass.Derived.LQGMeasureChartSmooth

/-!
# Cited inputs of the coordinate change of the LQG measure for all inverse charts

Two printed results, stated for the zero-boundary GFF on a disc, from which the simultaneous coordinate change at fixed
scale (`SheffieldWangDiscConformal`) and then `LQGMeasureChartStmt` are proved.

* `SheffieldWangEnvelope`: Sheffield–Wang, *Field-measure correspondence in Liouville quantum gravity almost surely
  commutes with all conformal maps simultaneously* (arXiv:1605.06171v2), Theorem 1.1 (p. 3; along `2^{-k}` this is
  Duplantier–Sheffield (2011), arXiv:0808.1560v2, Proposition 1.1, p. 5) and the envelope statement at the end of the
  proof of Theorem 1.2 (pp. 10-11): for each `N ≥ 1`, almost surely the measures
  `C̃(N) sup_{ε ∈ [2^{-(k+1)/N}, 2^{-k/N}]} exp(h̃_ε(z)) dz` and `C(N) inf_{ε ∈ [2^{-(k+1)/N}, 2^{-k/N}]} exp(h̃_ε(z)) dz`
  both converge weakly to `μ` as `k → ∞`, and `C̃(N)`, `C(N)` converge to `1` as `N → ∞`. The constants `C̃(N)`,
  `C(N)` are the ratios of Brownian expectations displayed on p. 10.
  How the Lean statement differs: `D` is a disc; the existence of constants `u N = 1/C̃(N)`, `l N = 1/C(N)` tending to
  `1` is asserted after the field is given (a weaker quantifier order); "for each `N`, almost surely" becomes "almost
  surely, for every `N`" (countably many `N`); weak convergence is inside `D` (`QuantumZipper.IsVagueLimitOn`), with
  the envelope density set to `0` where the largest averaging ball leaves `D`; the circle average is any continuous
  circle-average process of the field (`IsCircleProcess`).
* `ZeroBoundaryGFFLocalRegularity`: De Nitti–Schweiger, *Scaling limits for fractional polyharmonic Gaussian fields*
  (arXiv:2301.13781v4), Proposition 2.1 (p. 9): for a bounded Lipschitz domain `Ω ⊆ ℝ^d`, `s ≥ 0`, `s' < s − d/2` and
  `p, q ∈ [1, ∞]`, the fractional Gaussian field on `Ω` is almost surely an element of `B̂^{s'}_{p,q}(ℝ^d)`; for `s = 1`
  it is the Gaussian free field (§1). How the Lean statement differs: with `s = 1`, `d = 2`, `p = q = ∞`, the Lean
  states the consequence for test functions that Besov regularity `B^β_{∞,∞}` with `β ∈ (−1, 0)` gives through the
  Littlewood–Paley blocks (`|⟨Δ_j h, v⟩| ≲ 2^{−jβ} min(1, 2^{−j}/λ)` for `v = λ^{−2} η((· − x)/λ)` with `|η|`,
  `‖∇η‖ ≤ 1` supported in the unit disc, summed over `j`): on every compact subset of the disc and at small scales,
  `|⟨h, λ^{−2} η((· − x)/λ)⟩| ≤ C λ^α`, for every `α < 0` (the local Hölder–Besov regularity `C^α_loc` of
  Furlan–Mourrat, arXiv:1502.07335v3, Definition 2.1). Mathlib has no Besov spaces. The same bound also follows from
  the Hölder continuity of the gradient of the Green potential `(−Δ_D)⁻¹ h` (Kolmogorov–Chentsov, as printed in
  Duplantier–Sheffield (2011), proof of Proposition 3.1, p. 18).
-/

set_option autoImplicit false

noncomputable section

open scoped Classical

open MeasureTheory Filter Topology Set Metric
open scoped Distributions

namespace MatedCRT

open LQGMeasureChart

/-- **Cited input: Sheffield–Wang (2016), Theorem 1.1 and the envelope statement at the end of the proof of Theorem
1.2** (arXiv:1605.06171v2, pp. 3, 10-11), on a disc; see the module docstring. -/
def SheffieldWangEnvelope : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ f : ℂ → ℝ, IsMollifier f → ∀ (c : ℂ) (r : ℝ), 0 < r →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω), IsProbabilityMeasure P →
  ∀ h : Ω → LQGMetric.DistOn (disc c r), LQGMetric.IsZeroBoundaryGFF (disc c r) h P →
  ∀ hcirc : Ω → ℝ → ℂ → ℝ, (∀ᵐ ω ∂P, IsCircleProcess c r (h ω) (hcirc ω)) →
  ∃ u l : ℕ → ℝ, (∀ N, 0 < u N ∧ 0 < l N) ∧ Tendsto u atTop (𝓝 1) ∧ Tendsto l atTop (𝓝 1) ∧
    ∀ᵐ ω ∂P, ∃ μ : Measure ℂ,
      QuantumZipper.IsVagueLimitOn (ball c r)
        (fun k => HarmonicBalls.lqgApprox γ (hcirc ω) (HarmonicBalls.dyadicScale k)) μ ∧
      ∀ N : ℕ, 1 ≤ N →
        QuantumZipper.IsVagueLimitOn (ball c r)
          (fun k => envSup γ f (ball c r) (pairFun (h ω)) N k) (ENNReal.ofReal (u N) • μ) ∧
        QuantumZipper.IsVagueLimitOn (ball c r)
          (fun k => envInf γ f (ball c r) (pairFun (h ω)) N k) (ENNReal.ofReal (l N) • μ)

/-- **Cited input: the local negative regularity of the zero-boundary GFF on a disc** (De Nitti–Schweiger,
arXiv:2301.13781v4, Proposition 2.1, p. 9, with `s = 1`, `d = 2`, `p = q = ∞`, in its test-function form; see the
module docstring): almost surely, for every `α < 0` and every compact subset `K` of the disc, the pairings of `h`
with the test functions `t⁻² η((· − x)/t)`, `x ∈ K`, `0 < t ≤ t₀`, `η` smooth with `|η| ≤ 1`, `‖∇η‖ ≤ 1` and support in
the unit disc, are at most `C t^α`. -/
def ZeroBoundaryGFFLocalRegularity : Prop :=
  ∀ (c : ℂ) (r : ℝ), 0 < r → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω), IsProbabilityMeasure P →
  ∀ h : Ω → LQGMetric.DistOn (disc c r), LQGMetric.IsZeroBoundaryGFF (disc c r) h P →
  ∀ᵐ ω ∂P, ∀ α : ℝ, α < 0 → ∀ K : Set ℂ, IsCompact K → K ⊆ ball c r →
    ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ x ∈ K, ∀ t ∈ Ioc 0 t₀, ∀ η : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η →
      tsupport η ⊆ ball 0 1 → (∀ z, |η z| ≤ 1) → (∀ z, ‖fderiv ℝ η z‖ ≤ 1) →
      |pairFun (h ω) (fun y => (t ^ 2)⁻¹ * η ((y - x) / (t : ℂ)))| ≤ C * t ^ α

end MatedCRT
