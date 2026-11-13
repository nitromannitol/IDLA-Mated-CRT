import MatedCRT.Draft.Section3HarmonicCorrected

/-! # Pointwise same-walk rates on a given environment event -/

namespace MatedCRT

open MeasureTheory Set Metric _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- The quenched tail and mean estimates of the same-walk comparison of corrected
Lemma 3.6 at every environment of the event `E`, for given exponents. -/
def PointwiseSameWalkRatesStep {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (E : ℝ → Set Ω) (ρ a β ν : ℝ) : Prop :=
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ (ψ : ℂ → ℝ) (H χ : ℝ≥0), 0 < χ → χ ≤ 1 →
    HolderOnWith H χ ψ (closedBall z r) →
  ∀ q : ℝ, 0 < q → q < min a β * (χ : ℝ) →
  ∀ y ∈ ball z r, ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ ω ∈ E ε,
      ∀ v ∈ interiorCellVertices ε (S.η ω) (ball z r),
        (srwLaw (S.mult ε ω) v)
          {x | (1 + (H : ℝ)) * ε ^ q < sameWalkExitDiscrepancy S r z ψ ε ω x} ≤
            ENNReal.ofReal (C * ε ^ (ν * (min a β - q / χ))) ∧
        (∫ x, sameWalkExitDiscrepancy S r z ψ ε ω x ∂srwLaw (S.mult ε ω) v) ≤
          C * (H : ℝ) *
            (if (χ : ℝ) < ν then ε ^ (min a β * χ)
             else if (χ : ℝ) = ν then ε ^ (min a β * ν) * (1 + |Real.log ε|)
             else ε ^ (min a β * ν))

end MatedCRT
