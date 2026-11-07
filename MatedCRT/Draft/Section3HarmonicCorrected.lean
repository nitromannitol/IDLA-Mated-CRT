import MatedCRT.Steps.Sec3.ConvergenceHarmonicFunctions
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Corrected Lemma 3.6: harmonic convergence

The frozen `ConvergenceHarmonicFunctionsStmt` is not the corrected statement:
the latter uses continuous data on the closed disc and projects every exit-cell
representative onto that disc. See `LEMMA36-REPLACEMENT.md`, lines 105–119 and
491–589. The quantitative same-walk comparison is a separate assertion.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls InnerProductSpace
open scoped ENNReal NNReal

/-- The cellwise discrete harmonic extension with projected exit-cell values. -/
noncomputable def projectedDiscreteHarmonicExtension {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (r : ℝ) (z : ℂ) (ψ : ℂ → ℝ)
    (ε : ℝ) (ω : Ω) (y : ℂ) : ℝ :=
  ∫ x, ψ (ballRetraction z r (vertexPoint ε (S.η ω)
      (vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x)))
    ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)

/-- The pointwise and uniform convergence parts of corrected Lemma 3.6.
The deterministic limit is the classical harmonic extension of the boundary
data, and agrees almost surely with the rescaled LBM exit expectation. -/
def CorrectedHarmonicConvergenceStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ ψ : ℂ → ℝ, ContinuousOn ψ (closedBall z r) →
  ∃ u : ℂ → ℝ, ContinuousOn u (closedBall z r) ∧ HarmonicOnNhd u (ball z r) ∧
    (∀ x ∈ sphere z r, u x = ψ x) ∧
    (∀ y ∈ ball z r, (∀ᵐ ω ∂S.P,
      (∫ b, ψ (pathExitPosition (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b))
        ∂planarBrownianMotion y) = u y) ∧
      TendstoInProbability S.P (fun ε ω => projectedDiscreteHarmonicExtension S r z ψ ε ω y)
        (fun _ => u y)) ∧
    TendstoUniformlyOnInProbability S.P (projectedDiscreteHarmonicExtension S r z ψ)
      (fun _ => u) (closedBall z r)

end MatedCRT
