import MatedCRT.FirstPass.Derived.CanonicalCountedFormsOfCouplingClock

/-!
# Theorems 1.4 and 1.6 from the remaining premises

`convergenceOfIDLA_conditional` and `convergenceOfDivSandpile_conditional` (`MatedCRT/Assembly/Main.lean`) prove
Theorems 1.4 and 1.6 for every space-filling SLE model from the 42 fields of `MainHypotheses`. At the canonical model
`ProbeMi.canonicalSLEModel ν` (the curve modulo increasing reparametrization, with its Lebesgue-area representative)
the first-pass route (`docs/campaign/COUNTED.md`) proves them from the three premises collected in
`CanonicalHypotheses ν`; every other input of that route is proved in this repository, in Harmonic-Balls-LQG or in
Lattice-Probability.  The premises are:

* `matingOfTreesCoupling`: for every `0 < γ < 2`, a mating-of-trees coupling on `ℝ` (the record
  `IsMatingOfTreesCoupling` of Lattice-Probability; Duplantier-Miller-Sheffield, arXiv:1409.7055, Theorem 1.9) whose
  Lebesgue-parametrized curve has code law `ν (16 / γ²)`;
* `tutteLP`: the comparison of the stopped curves of the walk and of the space-filling SLE from every selected start,
  in Lévy-Prokhorov distance (the comparison established in the proof of Gwynne-Miller-Sheffield, arXiv:1705.11161,
  Theorem 3.4, case 1), for one valid environment of a model with law `ν`;
* `chartField`: `BG20ChartFieldInput`, the chart forms of Berestycki-Gwynne, arXiv:2003.10320, Lemmas 7.20 (the
  coordinate change of Liouville Brownian motion, Berestycki, arXiv:1301.3356, Theorem 1.3) and 7.21 (independence of
  the two windows, from Duplantier-Miller-Sheffield, Theorem 1.9).

## Main statements

* `CanonicalHypotheses`: the three premises.
* `convergenceOfIDLA_canonical`: Theorem 1.4 at the canonical model from `CanonicalHypotheses ν`.
* `convergenceOfDivSandpile_canonical`: Theorem 1.6 at the canonical model from `CanonicalHypotheses ν`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls _root_.LQGMetric _root_.MatedCRTHarmonic _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction

namespace MatedCRT

/-- The premises of Theorems 1.4 and 1.6 at the canonical space-filling SLE model `ProbeMi.canonicalSLEModel ν` that
are not proved in this repository or in the libraries it uses. -/
structure CanonicalHypotheses (ν : ℝ → Measure SLEPathCode) : Prop where
  /-- For every `0 < γ < 2`, a mating-of-trees coupling on `ℝ` whose Lebesgue-parametrized curve has code law
  `ν (16 / γ²)` (Duplantier-Miller-Sheffield, Theorem 1.9). -/
  matingOfTreesCoupling : ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
      (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
      IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
      P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2)
  /-- For every `0 < γ < 2`, a valid environment of a model with law `ν` whose walk and curve, stopped at their exit
  from `B_R(0)`, are close in Lévy-Prokhorov distance from every selected start, with probability tending to one
  (the comparison of the proof of Gwynne-Miller-Sheffield, Theorem 3.4, case 1). -/
  tutteLP : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
    ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
    ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
    ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        S₀.P.map (fun ω => (η₀ ω, S₀.mult (1 / (n : ℝ)) ω))
          (uniformStartSelectedLPData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ
  /-- The chart forms of Berestycki-Gwynne, Lemmas 7.20 and 7.21, at the canonical model. -/
  chartField : BG20ChartFieldInput (ProbeMi.canonicalSLEModel ν)

/-- **Theorem 1.4** (convergence of IDLA) at the canonical space-filling SLE model, from `CanonicalHypotheses ν`. -/
theorem convergenceOfIDLA_canonical (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) :
    ConvergenceOfIDLAStmt (ProbeMi.canonicalSLEModel ν) :=
  FirstPass.Derived.closed_1_4_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_chartField ν
    H.matingOfTreesCoupling H.tutteLP H.chartField

/-- **Theorem 1.6** (convergence of the divisible sandpile) at the canonical space-filling SLE model, from
`CanonicalHypotheses ν`. -/
theorem convergenceOfDivSandpile_canonical (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) :
    ConvergenceOfDivSandpileStmt (ProbeMi.canonicalSLEModel ν) :=
  FirstPass.Derived.closed_1_6_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_chartField ν
    H.matingOfTreesCoupling H.tutteLP H.chartField

end MatedCRT
