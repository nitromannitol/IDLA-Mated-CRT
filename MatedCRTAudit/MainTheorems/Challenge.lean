import MatedCRT.Draft.Section1
import MatedCRT.FirstPass.SLERef.CanonicalModel
import MatedCRT.FirstPass.Derived.HN9OfChartField
import MatedCRT.FirstPass.Derived.GMS21UniformStartOfSelectedProkhorov

/-!
# Theorems 1.4 and 1.6 at the canonical model: comparator challenge

Comparator challenge for the two main theorems of A. Bou-Rabee and E. Gwynne, *Internal DLA on
mated-CRT maps*, at the canonical space-filling SLE model `ProbeMi.canonicalSLEModel ν` (the curve
modulo increasing reparametrization): the convergence of IDLA (Theorem 1.4) and of the divisible
sandpile (Theorem 1.6) to the LQG harmonic balls.

The conclusions are the statements `ConvergenceOfIDLAStmt` and `ConvergenceOfDivSandpileStmt` of
`MatedCRT/Draft/Section1.lean`. Each theorem takes as explicit hypotheses the three premises that the
repository does not prove, in the form of the fields of `MatedCRT.CanonicalHypotheses`
(`MatedCRT/Assembly/Canonical.lean`):

* `hcpl`: for every `0 < γ < 2`, a mating-of-trees coupling on `ℝ` whose Lebesgue-parametrized
  curve has code law `ν (16 / γ²)` (Duplantier-Miller-Sheffield, arXiv:1409.7055, Theorem 1.9);
* `hTutteLP`: the comparison, in Lévy-Prokhorov distance, of the stopped curves of the walk and of
  the space-filling SLE from every selected start (the proof of Gwynne-Miller-Sheffield,
  arXiv:1705.11161, Theorem 3.4, case 1);
* `hchart`: the chart forms of Berestycki-Gwynne, arXiv:2003.10320, Lemmas 7.20 and 7.21
  (`BG20ChartFieldInput`).

This file imports the statement module `MatedCRT.Draft.Section1`, the canonical model and the modules
that define the vocabulary of the premises; it is not a mathlib-only restatement. The two proofs are
the intentional `sorry`s of this file; `Solution.lean` proves the same statements from the library.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls _root_.LQGMetric _root_.MatedCRTHarmonic _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction
open MatedCRT

namespace MatedCRTAudit.MainTheorems

/-- **Theorem 1.4** (convergence of IDLA) at the canonical space-filling SLE model, from the three
premises. -/
theorem convergence_of_idla (ν : ℝ → Measure SLEPathCode)
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2))
    (hTutteLP : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          S₀.P.map (fun ω => (η₀ ω, S₀.mult (1 / (n : ℝ)) ω))
            (uniformStartSelectedLPData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ)
    (hchart : BG20ChartFieldInput (ProbeMi.canonicalSLEModel ν)) :
    ConvergenceOfIDLAStmt (ProbeMi.canonicalSLEModel ν) :=
  sorry

/-- **Theorem 1.6** (convergence of the divisible sandpile) at the canonical space-filling SLE model,
from the three premises. -/
theorem convergence_of_div_sandpile (ν : ℝ → Measure SLEPathCode)
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2))
    (hTutteLP : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          S₀.P.map (fun ω => (η₀ ω, S₀.mult (1 / (n : ℝ)) ω))
            (uniformStartSelectedLPData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ)
    (hchart : BG20ChartFieldInput (ProbeMi.canonicalSLEModel ν)) :
    ConvergenceOfDivSandpileStmt (ProbeMi.canonicalSLEModel ν) :=
  sorry

end MatedCRTAudit.MainTheorems
