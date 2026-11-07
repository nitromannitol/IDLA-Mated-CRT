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

open Classical in
/-- The exit functional from the quantitative comparison, zero if the path
does not start inside the disc or never exits it. -/
noncomputable def finiteDiscExitValue (z : ℂ) (r : ℝ) (ψ : ℂ → ℝ)
    (w : ℝ≥0 → ℂ) : ℝ :=
  if w 0 ∈ ball z r ∧ pathExitTime (ball z r) w < ⊤ then
    ψ (pathExitPosition (ball z r) w)
  else 0

/-- The absolute discrepancy between the unrestricted interpolated walk and
the projected representative of its first exit cell. -/
noncomputable def sameWalkExitDiscrepancy {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (r : ℝ) (z : ℂ) (ψ : ℂ → ℝ)
    (ε : ℝ) (ω : Ω) (x : ℕ → ℤ) : ℝ :=
  |finiteDiscExitValue z r ψ (interpolatedWalk ε (S.η ω) (S.mε ε) x) -
    ψ (ballRetraction z r (vertexPoint ε (S.η ω)
      (vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x)))|

open Classical in
/-- The quantitative same-walk comparison in corrected Lemma 3.6. The event
is independent of the datum and starting vertex. The annulus exponent depends
only on `γ`; `ν` can also depend on the outer radius. The three mean-error
regimes and the annealed and quenched tail bounds are from
`LEMMA36-REPLACEMENT.md`, lines 340–379. -/
def CorrectedHarmonicSameWalkRateStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ bAnn : ℝ, 0 < bAnn ∧
  ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ a : ℝ, 0 < a → a < 2 / (2 + γ) ^ (2 : ℕ) →
  ∃ ν κ : ℝ, 0 < ν ∧ 0 < κ ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ E : ℝ → Set Ω, ∃ CE εE : ℝ, 0 ≤ CE ∧ 0 < εE ∧
    (∀ ε : ℝ, 0 < ε → ε < εE → S.P (E ε)ᶜ ≤ ENNReal.ofReal (CE * ε ^ κ)) ∧
    ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
    ∀ (ψ : ℂ → ℝ) (H χ : ℝ≥0), 0 < χ → χ ≤ 1 →
    HolderOnWith H χ ψ (closedBall z r) →
    ∀ q : ℝ, 0 < q → q < min a bAnn * (χ : ℝ) →
    ∀ y ∈ ball z r, ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        sectionwiseOuterProb S.P (fun ω => srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
          {p | (1 + (H : ℝ)) * ε ^ q < sameWalkExitDiscrepancy S r z ψ ε p.1 p.2} ≤
            ENNReal.ofReal (C * (ε ^ κ + ε ^ (ν * (min a bAnn - q / χ)))) ∧
        ∀ ω ∈ E ε, ∀ v ∈ interiorCellVertices ε (S.η ω) (ball z r),
          (srwLaw (S.mult ε ω) v)
            {x | (1 + (H : ℝ)) * ε ^ q < sameWalkExitDiscrepancy S r z ψ ε ω x} ≤
              ENNReal.ofReal (C * ε ^ (ν * (min a bAnn - q / χ))) ∧
          (∫ x, sameWalkExitDiscrepancy S r z ψ ε ω x ∂srwLaw (S.mult ε ω) v) ≤
            C * (H : ℝ) *
              (if (χ : ℝ) < ν then ε ^ (min a bAnn * χ)
               else if (χ : ℝ) = ν then ε ^ (min a bAnn * ν) * (1 + |Real.log ε|)
               else ε ^ (min a bAnn * ν))

/-- The full corrected Lemma 3.6, including its quantitative comparison. -/
def CorrectedLemma36Stmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  CorrectedHarmonicConvergenceStmt 𝒮 ∧ CorrectedHarmonicSameWalkRateStmt 𝒮

end MatedCRT
