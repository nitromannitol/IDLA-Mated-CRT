import MatedCRT.Steps.Sec3.PointwiseSameWalkRates

/-! # The annealed same-walk rate component -/

namespace MatedCRT

open MeasureTheory Set Metric _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- The annealed tail component, at fixed model parameters and exponents. -/
def AnnealedSameWalkRateStep {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (ρ a β ν κ : ℝ) : Prop :=
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ (ψ : ℂ → ℝ) (H χ : ℝ≥0), 0 < χ → χ ≤ 1 →
    HolderOnWith H χ ψ (closedBall z r) →
  ∀ q : ℝ, 0 < q → q < min a β * (χ : ℝ) →
  ∀ y ∈ ball z r, ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      sectionwiseOuterProb S.P (fun ω => srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
        {p | (1 + (H : ℝ)) * ε ^ q < sameWalkExitDiscrepancy S r z ψ ε p.1 p.2} ≤
          ENNReal.ofReal (C * (ε ^ κ + ε ^ (ν * (min a β - q / χ))))

end MatedCRT
