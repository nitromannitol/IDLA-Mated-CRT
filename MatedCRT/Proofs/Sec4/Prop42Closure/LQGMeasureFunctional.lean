import MatedCRT.Proofs.Sec4.Prop42Closure.ConeWholePlaneSteps

/-! # Locality of the LQG measure as a functional of the restricted field: the input (A) of gap G1 (now proved)

Operator ruling (2026-11-08, `tasks/z5.md`, item (A)): the locality input of the restricted-law derivation is a named
Step Prop with exactly the type of `LQGMeasureLocalityFunctionalStep` below. It was an open input. It is now proved, with
no literature hypothesis, by `LQGMeasureLocalityFunctionalStep_proof` (`LQGMeasureLocalityProof.lean`; steps2:651-794,
audited CORRECT as declared, `notes/wpn-steps2/AUDIT-steps2.md` target 4; commit 48b2c75). It is not a staged literature
statement: it is not in `MatedCRT/External` or `MatedCRT/Proposed`, and it is not weakened anywhere. The reduced-input
consumer `coneWholePlaneRestrictedLQGLawStep_of_fieldLaw` (`ConeWholePlaneRestrictedLaw.lean`) and the reduced-input
consumers `conePrematureContactNullStep_of_fieldLaw` and `coneHalfBallClosureInsideStep_of_fieldLaw` (`ConePrematureNull.lean`)
supply the proof internally. The `_of_inputs` versions (`coneWholePlaneRestrictedLQGLawStep_of_inputs`,
`conePrematureContactNullStep_of_inputs`, `coneHalfBallClosureInsideStep_of_inputs`) keep the Step as an explicit
hypothesis, for compatibility.

**Sources.** IDLA paper (`paper/idla_mated_crt-corrected.tex`), Fact (LQG measure) II, "Locality" (lines 478-480): for
every deterministic open `U ⊂ ℂ`, `μ_h(U)` is given by a measurable function of `h|_U`. Line 492 of the same paper says
that the first three properties of that Fact are "immediate from the definition" (eq:measure-lim, line 396). The paper
cites no reference for locality; its citations in the same paragraph (line 492) (Duplantier-Sheffield 2011, Prop. 2.1, and Sheffield
2016) concern conformal covariance (property IV), not locality.

**Difference from Harmonic-Balls `LQGMeasureLocality`** (`HarmonicBalls/Proposed/LQG.lean:83`; repository copy
`LQGMeasureLocalityPart`, `Steps/Sec2/LQGMeasureProperties.lean:45`). That input gives, for each field separately, some
`Y` which is measurable with respect to `σ(h|_U)` and satisfies `μ(U) = Y` a.s. It is an existence statement, and `Y`
depends on the instance. Equal laws of the restricted fields do not give equal laws of `μ(U)` from it, because equal laws
of `F` do not fix the joint law of `(F, μ(U))`. The statement below asks for one measurable functional `Λ`, fixed by
`U` and `γ`, which serves both the cone field `h` of `IsConeField` (circle averages `hcirc`) and the whole-plane field
`h^ℂ - γ log|·|` of `IsWholePlaneGFF` with its `γ`-LQG measure `IsLQGMeasureOfField P' γ γ` (circle averages
`fieldCircleAverage γ`). This common functional is what the paper's phrase "given by a measurable function of `h|_U`"
asserts for the two models; I did not use the Harmonic-Balls existence statement in its place. -/

namespace MatedCRT

open MeasureTheory Metric HarmonicBalls
open scoped ENNReal

/-- **(A) Locality of the γ-LQG measure as a functional of the restricted field** (proved: `LQGMeasureLocalityFunctionalStep_proof`,
`LQGMeasureLocalityProof.lean`; paper Fact (LQG measure) II, lines 478-480; see the module docstring for the sources and for
how it differs from Harmonic-Balls `LQGMeasureLocality`).

For every `γ ∈ (0, 2)` and every open `U ⊆ B_1`, there is one measurable functional `Λ` of the restricted field
`h|_{B_1}` (pairings on `TestB1`, circle averages on `CircleB1`) such that `μ(U) = Λ(h|_{B_1})` almost surely, at the
same time for the cone field (`IsConeField γ P hC hcirc μ`, restricted by `coneFieldOnB1`) and for the whole-plane field
`h^ℂ - γ log|·|` (`IsWholePlaneGFF P' hC' hcirc'` with `IsLQGMeasureOfField P' γ γ hcirc' μ'`, restricted by
`wholePlaneFieldOnB1 γ`). The restricted field is the pair of pairings on test functions supported in `B_1` (`TestB1`) and
of circle averages over region circles in `B_1` (`CircleB1`). -/
def LQGMeasureLocalityFunctionalStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ U : Set ℂ, IsOpen U → U ⊆ ball (0 : ℂ) 1 →
    ∃ Λ : ((TestB1 → ℝ) × (CircleB1 → ℝ)) → ℝ≥0∞, Measurable Λ ∧
      (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
          (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
          IsConeField γ P hC hcirc μ → ∀ᵐ ω ∂P, μ ω U = Λ (coneFieldOnB1 hC hcirc ω)) ∧
      (∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
          (hcirc' : Ω' → ℝ → ℂ → ℝ) (μ' : Ω' → Measure ℂ),
          IsProbabilityMeasure P' → IsWholePlaneGFF P' hC' hcirc' → IsLQGMeasureOfField P' γ γ hcirc' μ' →
            ∀ᵐ ω' ∂P', μ' ω' U = Λ (wholePlaneFieldOnB1 γ hC' hcirc' ω'))

end MatedCRT
