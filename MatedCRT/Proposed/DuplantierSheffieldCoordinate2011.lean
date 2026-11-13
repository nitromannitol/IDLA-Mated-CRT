import HarmonicBalls.Defs.LQG
import MatedCRT.Defs.DirichletGFF
import MatedCRT.Proofs.Sec4.Prop42Closure.InsertionCoordinate

/-!
# Staged cited inputs: Duplantier-Sheffield 2011 (arXiv:0808.1560v2), zero-boundary GFF measure and coordinate rule

STAGING FILE (`MatedCRT/Proposed/`). Nothing here is proved, promoted or postulated. Each cited result is a `Prop`-valued
definition, used only as an explicit hypothesis. The printed statement is source-checked before any move to
`MatedCRT/External`.

## Printed sources (PDF page numbers of arXiv:0808.1560v2, re-checked 2026-11-08 against the PDF)

* Setup, p. 3: "let h be an instance of a centered GFF on a bounded simply connected domain D with zero boundary conditions".
* Normalization, p. 4: the Dirichlet form is `(f₁, f₂)∇ := (2π) ∫ ∇f₁·∇f₂`, and "the two point covariance scales like
  `-log|z - w|` instead of `-(2π)⁻¹ log|z - w|`". So the covariance is `2π` times the Green function with `-ΔG = δ`, the
  normalization of `MatedCRT.dirichletGFFCovariance`.
* Circle averages, p. 4: "let h_ε(z) denote the mean value of h on ∂B_ε(z) ... (where h(z) is defined to be zero for z ∈ ℂ \ D)".
* Proposition 1.1, **p. 5** (the previous header said p. 4; p. 4 carries the circle-average convention): "Fix γ ∈ [0, 2) and
  define the zero boundary GFF h and D as above. Then it is almost surely the case that as ε → 0 along powers of two, the
  measures μ_ε := ε^{γ²/2} e^{γ h_ε(z)} dz converge weakly inside D to a limiting measure, which we denote by μ = μ_h =
  e^{γh(z)} dz. This remains true if we replace h with a non-centered GFF on D — i.e., if we set h = h̃ + h₀ ... where h₀ is a
  deterministic, non-zero continuous function on D."
* Proposition 2.1, p. 13: "Let h be an instance of the GFF on D and ψ a conformal map from a domain D̃ to D. Write h̃ for the
  distribution on D̃ given by h ∘ ψ + Q log|ψ′| where Q = 2/γ + γ/2. Then μ_h is almost surely the image under ψ of the
  measure μ_h̃ on D̃. That is, μ_h̃(A) = μ_h(ψ(A)) for each Borel measurable A ⊂ D̃." Its proof (pp. 13-14) uses the
  conformal invariance of (·,·)∇ and the approximations µ_n of Proposition 1.2 (not staged here).

## Source-status corrections

* The former declaration `DS11CoordinateRuleFixedAffine` (commit 9e51e0c) was presented as DS11 Prop. 2.1. It is NOT that
  statement. It is the open internal extension `InsertionCoordinateExtensionStep`; the old
  name is kept only as an abbreviation so that existing consumers still compile.
* DS11 Prop. 2.1 is NOT staged as a Prop here. Its conclusion needs the circle averages of the pulled-back field `h ∘ ψ`, which the
  repository carriers cannot express (see the block "Not staged" at the end).
* `DS11Prop11ZeroBoundaryMeasure` is the printed Prop. 1.1, with its printed normalization, on the repository carrier
  `MatedCRT.IsDirichletGFF`.
* Sheffield–Wang, arXiv:1605.06171v2 (scope identified from the PDF text; not staged here). Setup, p. 2: `D` a bounded simply
  connected domain. Thm 1.1, p. 3: all-scale a.s. weak convergence of `e^{h̄_ε(z)} dz`, `h̄_ε = γ h_ε + (γ²/2) log ε` (1.3, p. 2).
  Thm 1.4, p. 3: for `γ ∈ [0,2)`, almost surely, for all conformal `φ : D̃ → D` with `D̃` any planar domain (`Λ`, (1.5)), the
  measures `μ_{h̃_φ}` for `h̃_φ = h∘φ + Q log|φ′|` (1.6) are well-defined and `μ_h(A) = μ_{h̃_φ}(φ⁻¹(A))` for Borel `A ⊂ D`,
  simultaneously for all `φ` (1.7). Its measures are defined by the mollifier correspondence (1.2), (1.4) (pp. 2-3), not by the
  circle averages of DS11 Prop. 1.1. SW Prop. 2.3, p. 5: `h∘φ`, defined by `(h∘φ, ρ̃) := (h, |(φ⁻¹)′|² ρ̃∘φ⁻¹)`, is a
  zero-boundary GFF on `D̃`. SW Remark 3.3, p. 11: `(h∘φ) ∗ f_ε(z) = ⟨h, |(φ⁻¹)′|² f_ε(z − φ⁻¹(·))⟩`, a test-function pairing.
  SW p. 2: DS11 used the uniform measure on the unit circle as the mollifier `f`.
* NORMALIZATION FLAG N1 (unresolved). SW (1.2), p. 2, displays the exponent `γ h∗f_ε(z) − (γ²/2) E|h∗f_ε(z)|²`. With
  `E h_ε(z)² = −log ε + log C(z;D)` (SW (2.3), p. 5; DS11 p. 5) this is `ε^{γ²/2} C(z;D)^{−γ²/2} e^{γ h_ε(z)}`, which differs by
  `C(z;D)^{−γ²/2}` from DS11 Prop. 1.1 and SW (1.3), `ε^{γ²/2} e^{γ h_ε(z)}`. DS11 Prop. 1.2 eq. (1), p. 5, carries the
  compensating `+(γ²/2) log C(z;D)`. The page image of SW (1.2) must be checked before any mollifier-based staging. The
  circle-average normalization used here is DS11 Prop. 1.1.

## Scope notes (printed scope, not extended here)

* SCOPE-γ: Prop. 2.1 defines `Q = 2/γ + γ/2`, which is undefined at `γ = 0`; the printed range of Prop. 1.1 is `γ ∈ [0,2)`.
  Any statement using `Q` needs `0 < γ < 2`.
* SCOPE-D: Prop. 1.1 and the approximations of Prop. 1.2 are printed for a bounded simply connected `D` (pp. 3, 5). Prop. 2.1
  applies the same construction to `μ_h̃` on an arbitrary domain `D̃` (for example a half-plane when `D` is the unit disc). That
  extension is not printed.
* SCOPE-N: the printed circle averages use `h := 0` off `D` (p. 4). The inside-`D` limit below tests only circles inside `D` for
  small `ε`, so the convention off `D` is not used.
-/

namespace MatedCRT.Proposed

open MeasureTheory Filter Topology HarmonicBalls

/-- **Normalization of DS11 Prop. 1.1 (p. 5): `m` is the weak limit inside `D` of `ε^{γ²/2} e^{γ h_ε(z)} dz`.**
`DS11IsLQGLimitInside D γ hε m`: `hε ε z` is the circle average `h_ε(z)` (p. 4). The approximations are
`lqgApprox γ hε (dyadicScale k)`, that is, along the powers of two `ε = 2^{-k}`. The limit `m` is a locally finite measure on
`D` such that, for every continuous `f` with compact support contained in `D`, the integrals against the approximations converge
to the integral against `m`. -/
structure DS11IsLQGLimitInside (D : Set ℂ) (γ : ℝ) (hε : ℝ → ℂ → ℝ) (m : Measure ℂ) : Prop where
  /-- The limit is locally finite. -/
  isLocallyFiniteMeasure : IsLocallyFiniteMeasure m
  /-- The limit is a measure on `D` (`μ = e^{γh}dz` on `D`, p. 5). -/
  measure_compl : m Dᶜ = 0
  /-- Weak convergence inside `D` along the powers of two. -/
  tendsto_integral : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ D →
    Tendsto (fun k : ℕ => ∫ z, f z ∂(lqgApprox γ hε (dyadicScale k))) atTop (𝓝 (∫ z, f z ∂m))

/-- **Staged cited input: DS11 Prop. 1.1 (p. 5), with the printed normalization.** For `γ ∈ [0,2)`, a bounded simply connected
open set `D` (p. 3) and a zero-boundary GFF `hD` with circle averages `hcirc` (`MatedCRT.IsDirichletGFF`): almost surely the
measures `ε^{γ²/2} e^{γ h_ε(z)} dz` converge weakly inside `D` along the powers of two to a limiting measure (first conjunct).
The same holds for `h + h₀` with `h₀` deterministic and continuous on `D`, through `addCircleAverage` (second conjunct, p. 5). -/
def DS11Prop11ZeroBoundaryMeasure : Prop :=
  ∀ γ : ℝ, 0 ≤ γ → γ < 2 →
  ∀ (D : Set ℂ), IsOpen D → SimplyConnectedSpace D → Bornology.IsBounded D →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hD : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    IsProbabilityMeasure P → MatedCRT.IsDirichletGFF P D hD hcirc →
    (∃ μ : Ω → Measure ℂ, ∀ᵐ ω ∂P, DS11IsLQGLimitInside D γ (hcirc ω) (μ ω)) ∧
    ∀ h₀ : ℂ → ℝ, ContinuousOn h₀ D →
      ∃ μ₀ : Ω → Measure ℂ, ∀ᵐ ω ∂P, DS11IsLQGLimitInside D γ (addCircleAverage (hcirc ω) h₀) (μ₀ ω)

/-- **Backwards-compatible alias of the exact internal Step `MatedCRT.InsertionCoordinateExtensionStep`**
(`MatedCRT/Proofs/Sec4/Prop42Closure/InsertionCoordinate.lean`, the former declaration of this file). It is the open internal
extension (not a DS11 citation); its statement is unchanged and it is not proved.

For `γ ∈ (0,2)` and `α < Q`, every whole-plane GFF `h^ℂ` (`hC`, `hcirc`) on a probability space whose insertion-`α` LQG measure
is `μ` (`IsLQGMeasureOfField`), and every complex affine map `φ(z) = a z + b` with `a ≠ 0`: almost surely the circle averages
`(ε, z) ↦ h_{|a|ε}(a z + b) + Q log|a|` converge vaguely to `μ ∘ φ⁻¹ = μ.map (fun x => (x - b)/a)` along all `ε → 0`
(`IsLQGLimit`).

Why this is an extension and not a citation (exact scope of DS11 Prop. 2.1, p. 13):
* FIELD: DS11 Prop. 2.1 concerns a zero-boundary GFF on a bounded simply connected domain (p. 3). The whole-plane field with
  insertion `α` (`h^ℂ - α log|·|`, singular at `0`) is not covered by it or by Prop. 1.1, which needs `h₀` continuous on `D` (p. 5).
* SCALES: `IsLQGLimit` tests the approximations along `ε = 2^{-k}`, so the rescaled field is tested at radii `|a| 2^{-k}`. For
  `|a| ∉ 2^ℤ` these are non-dyadic scales, which Prop. 1.1 (powers of two, p. 5) does not print.
* MAPS: the printed rule is for conformal maps between domains, with `h̃ = h∘ψ + Q log|ψ′|` and `μ_h̃(A) = μ_h(ψ(A))`. The
  affine whole-plane case is outside its printed scope (FIELD above).

The theorem `insertionLQGScalingLawStep_of_coordinateRule` is conditional on this Prop. It is not promoted to `External`. -/
abbrev InsertionCoordinateExtensionStep : Prop := MatedCRT.InsertionCoordinateExtensionStep

/-- Legacy name of `InsertionCoordinateExtensionStep` (the former declaration of commit 9e51e0c), kept only so that existing
consumers compile. It is NOT the DS11 Prop. 2.1 statement and must not be cited as DS11. -/
abbrev DS11CoordinateRuleFixedAffine : Prop := InsertionCoordinateExtensionStep

/-! ## Not staged: DS11 Prop. 2.1 (p. 13). Exact missing carrier interfaces

Prop. 2.1 is a faithful Prop only with the following repository objects. None exists in `HarmonicBalls` or `MatedCRT`.

* (B1) Pairing of the zero-boundary field with finite-energy measures on `D`, and the pulled-back circle coupling. The pulled-back
  field `h̃ = h ∘ ψ + Q log|ψ′|` is the printed definition (p. 13). Its test-function rule is `(h∘ψ, |ψ′|²·(ρ∘ψ)) = (h, ρ)`
  (the pullback of p. 13 with `φ = ψ⁻¹`), so for a measure `ν` on `D̃`, `(h∘ψ, ν) = (h, ψ_*(|ψ′|² ν))`. The circle averages of
  `h̃`, which define `μ_h̃`, are therefore pairings of `h` with the image `ψ_*(‖deriv ψ‖² · σ_{z,r})` on `D`, where `σ_{z,r}` is the
  normalized arc length on `∂B_r(z)`. That image is a measure on a curve, not a test function. The carrier
  `HarmonicBalls.GFFObservable` (HarmonicBalls/Defs/GFF.lean:44-48) has only the constructors `pairing φ` (test functions) and
  `circle r z`, and `MatedCRT.IsDirichletGFF` carries only test-function pairings `hD : Ω → (ℂ → ℝ) → ℝ` and circle averages
  `hcirc`. Required interface (Lean-level, to be specified):
  - `hν : Ω → (finite signed measure ν on ℂ with finite Dirichlet energy and support in D) → ℝ`, extending `hD` on test functions;
  - (i) `hν ω (φ · volume) = hD ω φ` for test functions `φ` in `D`;
  - (ii) `hν ω σ_{z,r} = hcirc ω r z` a.s. for `closedBall z r ⊆ D`;
  - (iii) covariance `cov[hν · ν, hν · ν'] = ∫∫ 2π · greenFunction D x y dν dν'` (HarmonicBalls/Defs/Green.lean:70);
  - (iv) for a conformal bijection `ψ : D̃ → D` and `closedBall z r ⊆ D̃`, almost surely
    `hcircT ω r z = hν ω (Measure.map ψ ((‖deriv ψ ·‖ ^ 2) • σ_{z,r})) + Q * Real.circleAverage (fun w => Real.log ‖deriv ψ w‖) z r`.
  SW Prop. 2.3 (p. 5) prints the pathwise test-function pullback, and SW Remark 3.3 (p. 11) writes the pulled-back mollified
  field as a test-function pairing. A mollifier-based definition of `μ_h̃` would therefore need only test-function pairings,
  once the normalization flag N1 is settled. Item (iv) is not printed for circle averages.
* (B2) Conformal invariance of the covariance: `∀ x y ∈ D̃, greenFunction D̃ x y = greenFunction D (ψ x) (ψ y)`. It is needed so
  that `h ∘ ψ` is an `IsDirichletGFF P D̃`, and so that `DS11Prop11ZeroBoundaryMeasure` applies to `μ_h̃`. DS11 p. 13 uses the
  same invariance ("conformal invariance of (·,·)∇"). SW Prop. 2.3 (p. 5) prints the law: `h∘φ` is a zero-boundary GFF on
  `D̃` for a conformal `φ : D̃ → D` with `D̃` a planar domain. The covariance identity is not printed in that form. No such lemma
  is in `HarmonicBalls/Defs/Green.lean`.
* (S1) Prop. 1.1 for an unbounded simply connected `D̃` (SCOPE-D). DS11 does not print it. SW Thm 1.4 (p. 3) asserts that the
  measures `μ_{h̃_φ}` are well-defined for every planar `D̃` in `Λ`, but with SW's mollifier correspondence, not DS11's circle
  averages. Closing S1 for the DS11 measure depends on the normalization flag N1: a pending decision.
-/

end MatedCRT.Proposed
