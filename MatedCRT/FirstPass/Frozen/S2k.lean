import Mathlib.MeasureTheory.Measure.Regular
import HarmonicBalls.Defs.LQG

/-! # FIRST PASS Frozen statements for S2k (task fp-S2k-closure-inside)

Each `def` below is an EXTERNAL fact used as an explicit hypothesis. Nothing here is about this paper's clusters,
odometers, harmonic balls or IDLA processes: the statements concern general measure theory and the whole-plane GFF and
its LQG measure. -/

namespace MatedCRT.FirstPass.S2k

open MeasureTheory HarmonicBalls

/-- FIRST-PASS FROZEN. Lusin's theorem for finite Borel measures on complete separable metric spaces, in the form
used by the Borel full-law transfer (cycle note section 3.1). For a finite Borel measure `P` on a complete separable
metric space `X`, a Borel map `F` into a separable metric space `Y`, and every `ε > 0`, there is a compact `K ⊆ X`
with `P Kᶜ < ε` such that `F|K` is continuous. Source: Kechris, *Classical Descriptive Set Theory* (1995), Theorem 17.11
(tightness of Borel measures on Polish spaces, p. 107) and Theorem 17.12 (Lusin's theorem, p. 108). Locator taken from
`notes/fp-gaps/CHATGPT-closure-inside-cycle.md` section 2; the printed page is not verified by this file.
Used by: firstPass_exists_borel_image_fullLaw (`S2k/BorelTransfer.lean`). -/
def FrozenLusinCompactContinuity : Prop :=
  ∀ (X Y : Type) [MetricSpace X] [CompleteSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
    (P : Measure X) [IsFiniteMeasure P] (F : X → Y), Measurable F →
    ∀ ε : ENNReal, 0 < ε → ∃ K : Set X, IsCompact K ∧ P Kᶜ < ε ∧ ContinuousOn F K

/-- FIRST-PASS FROZEN (TRUE as typed; truth note notes/fp-gaps/CHATGPT-idla-K-S2h-S2k-truth.md §1). The insertion-`α` coordinate rule for fixed complex affine maps, at all real
scales: restated from `MatedCRT.InsertionCoordinateExtensionStep` (`Proofs/Sec4/Prop42Closure/InsertionCoordinate.lean:37`,
input K of the Proposition 4.2 plateau argument), with the same body. For `0 < γ < 2`, `α < Q`, a probability space carrying a
whole-plane GFF `(hC, hcirc)` whose insertion-`α` LQG measure is `μ`, and every affine map `z ↦ a z + b` with `a ≠ 0`, almost
surely the circle averages `(ε, z) ↦ h_{|a|ε}(a z + b) + Q log|a|` converge vaguely to `μ ∘ φ⁻¹` along all dyadic scales.
Locators: Harmonic-Balls arXiv:2208.11795v3, Fact 2.1 and equation (2.7), printed p. 9 (normalized log-GFF scaling and GMC
covariance); Duplantier-Sheffield arXiv:0808.1560v2, Proposition 2.1, printed p. 13 (coordinate change of the LQG measure under
conformal maps, `h̃ = h∘ψ + Q log|ψ′|`) and Proposition 1.1, p. 5. The whole-plane affine case at non-dyadic scales is not printed
in those places (see `Proposed/DuplantierSheffieldCoordinate2011.lean`, docstring of `DS11CoordinateRuleFixedAffine`), so the
statement is not literally DS11 Proposition 2.1. It is a corollary of standard GFF/GMC facts: the dyadic limit has a measurable
decoder, the insertion measure has no atom at `0`, convergence holds away from `0`, the limit is identified along each `R 2^{-n}`,
and the affine change of variables applies (truth note §1, steps A–E).
Used by: firstPass_plateauScaleInvarianceStep (`S2k.lean`, through `insertionLQGScalingLawStep_of_coordinateRule`). -/
def FrozenInsertionCoordinateRule : Prop :=
  ∀ (γ α : ℝ), 0 < γ → γ < 2 → α < lqgQ γ →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsProbabilityMeasure P → IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α hcirc μ →
  ∀ a : ℂ, a ≠ 0 → ∀ b : ℂ, ∀ᵐ ω ∂P,
    IsLQGLimit γ (fun ε z => fieldCircleAverage α (hcirc ω) (‖a‖ * ε) (a * z + b) + lqgQ γ * Real.log ‖a‖)
      ((μ ω).map fun x => (x - b) / a)

end MatedCRT.FirstPass.S2k
