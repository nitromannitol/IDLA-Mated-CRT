import MatedCRT.Draft.Section1
import MatedCRT.FirstPass.SLERef.CanonicalModel
import MatedCRT.FirstPass.Derived.HN9OfChartField
import MatedCRT.FirstPass.Derived.GMS21UniformStartOfSelectedProkhorov
import MatedCRT.Assembly.Canonical

/-!
# Theorems 1.4 and 1.6 at the canonical model: comparator solution

Proves the two statements of `MatedCRTAudit/MainTheorems/Challenge.lean` from
`MatedCRT.convergenceOfIDLA_canonical` and `MatedCRT.convergenceOfDivSandpile_canonical`
(`MatedCRT/Assembly/Canonical.lean`), whose hypothesis `CanonicalHypotheses ν` is the structure of the
three premises.
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
  convergenceOfIDLA_canonical ν ⟨hcpl, hTutteLP, hchart⟩

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
  convergenceOfDivSandpile_canonical ν ⟨hcpl, hTutteLP, hchart⟩

end MatedCRTAudit.MainTheorems
