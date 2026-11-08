import HarmonicBalls.Defs.LQG

/-!
# Staged cited input: LQG conformal covariance for affine maps (Duplantier-Sheffield 2011, Prop. 2.1)

STAGING FILE (`MatedCRT/Proposed/`). The operator source-checks the statement below before any promotion to
`MatedCRT/External`. Nothing in this file is proved: `DS11CoordinateRuleFixedAffine` is a named hypothesis, never an axiom.

## Printed sources (checked 2026-11-08)

* Duplantier-Sheffield, *Liouville quantum gravity and KPZ*, arXiv:0808.1560v2 (Dec. 2010), Proposition 2.1, p. 13.
  Verbatim: "Let h be an instance of the GFF on D and ψ a conformal map from a domain D̃ to D. Write h̃ for the
  distribution on D̃ given by h∘ψ + Q log|ψ′| where Q = 2/γ + γ/2. Then μ_h is almost surely the image under ψ of the
  measure μ_h̃ on D̃. That is, μ_h̃(A) = μ_h(ψ(A)) for each Borel measurable A ⊂ D̃."
* Same paper, Proposition 1.1, p. 4: for the zero-boundary GFF `h` on a domain `D` and `γ ∈ [0,2)`, the measures
  `ε^{γ²/2} e^{γ h_ε(z)} dz` converge weakly inside `D` "as ε → 0 along powers of two" to `μ_h`; the statement extends to
  `h = h₀ + h̃` with `h₀` deterministic and continuous on `D`.
* The paper, `paper/idla_mated_crt-corrected.tex`, `fact:lqg-measure` (lines 474-490), item IV, eq. `measure-coord`:
  `μ_{h∘φ+Q log|φ′|}(A) = μ_h(φ(A))` for open `U, Ũ` and a conformal map `φ : Ũ → U`, almost surely. This is the
  statement the insertion-`α` scaling law uses.
* Harmonic-Balls-LQG, `HarmonicBalls/Proposed/LQG.lean:114`, `LQGMeasureCoordChange`: the same rule for complex affine
  maps and whole-plane insertion fields (not promoted there either).

## SCOPE GAP (for the operator; not resolved here)

The printed Proposition 2.1 is for a zero-boundary GFF on a domain, with `μ_h` defined along powers of two (Prop. 1.1).
It does not print (i) the whole-plane field with insertion `α` (`h^ℂ - α log|·|`, singular at `0`, outside Prop. 1.1's
continuous `h₀`), nor (ii) the approximation scales `|a| 2^{-k}` for `|a| ∉ 2^ℤ`, which the circle-average approximations
of `IsLQGLimit` use. The statement below is the fixed affine-map form of the paper's `fact:lqg-measure` IV for the
insertion field. Its whole-plane insertion and non-dyadic extension is not in DS11 Prop. 2.1. The other cited source,
Sheffield-Wang (arXiv:1605.06171v2, Thm 1.1 and Thm 1.4: a.s. convergence as `ε → 0` and simultaneous covariance), is for
the bounded-domain Dirichlet field and has not been source-checked for the whole-plane insertion case.
-/

namespace MatedCRT.Proposed

open MeasureTheory HarmonicBalls

/-- **Staged cited input `DS11CoordinateRuleFixedAffine`** (see the file header for the printed sources and the scope gap).

For `γ ∈ (0,2)` and `α < Q = lqgQ γ`, every whole-plane GFF `h^ℂ` (`hC`, `hcirc`) on a probability space whose insertion-`α`
LQG measure is `μ` (`IsLQGMeasureOfField`), and every complex affine map `φ(z) = a z + b` with `a ≠ 0`: almost surely the
circle averages `(ε, z) ↦ h_{|a| ε}(a z + b) + Q log |a|` of `h ∘ φ + Q log|a|` converge vaguely to the image
`μ ∘ φ⁻¹ = μ.map (fun x => (x - b)/a)` along all `ε → 0` (`IsLQGLimit`). This is the fixed-map form, for one `φ`, of the
printed conformal covariance; the simultaneous-in-`φ` form is not needed. -/
def DS11CoordinateRuleFixedAffine : Prop :=
  ∀ (γ α : ℝ), 0 < γ → γ < 2 → α < lqgQ γ →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsProbabilityMeasure P → IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α hcirc μ →
  ∀ a : ℂ, a ≠ 0 → ∀ b : ℂ, ∀ᵐ ω ∂P,
    IsLQGLimit γ (fun ε z => fieldCircleAverage α (hcirc ω) (‖a‖ * ε) (a * z + b) + lqgQ γ * Real.log ‖a‖)
      ((μ ω).map fun x => (x - b) / a)

end MatedCRT.Proposed
