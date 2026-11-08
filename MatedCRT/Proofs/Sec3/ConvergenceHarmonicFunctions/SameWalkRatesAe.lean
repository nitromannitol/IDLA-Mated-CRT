import MatedCRT.Steps.Sec3.PointwiseSameWalkRates

/-! # Almost-everywhere same-walk rates (internal successors of the pointwise statements)

Repaired quenched rates of `notes/wpn-steps2/steps2-r2.tex`, Section 3 (lines 525–532 and 749–766). The pointwise
environment quantifier `∀ ω ∈ E ε` is replaced by `∀ᵐ ω ∂S.P, ω ∈ E ε → …`; the null set may depend on `ε`. Every
other quantity is copied verbatim: the constants `C, ε₀`, the exponents `a, β, ν, κ, q, χ`, the event `E` with its
polynomial complement, the sectionwise annealed bound and the three mean regimes. The frozen declarations
`PointwiseSameWalkRatesStep` and `CorrectedHarmonicSameWalkRateStmt` are not changed; the literal pointwise
form is false (steps2-r2.tex, proposition at lines 491–512). -/

namespace MatedCRT

open MeasureTheory Filter Set Metric _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- Almost-everywhere successor of `PointwiseSameWalkRatesStep`. Only the environment quantifier changes: for each
small mesh, `S.P`-almost every `ω` in `E ε` satisfies the tail and mean bounds at every interior label `v`. -/
def PointwiseSameWalkRatesAeStep {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (E : ℝ → Set Ω) (ρ a β ν : ℝ) : Prop :=
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ (ψ : ℂ → ℝ) (H χ : ℝ≥0), 0 < χ → χ ≤ 1 →
    HolderOnWith H χ ψ (closedBall z r) →
  ∀ q : ℝ, 0 < q → q < min a β * (χ : ℝ) →
  ∀ y ∈ ball z r, ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ᵐ ω ∂S.P, ω ∈ E ε →
        ∀ v ∈ interiorCellVertices ε (S.η ω) (ball z r),
          (srwLaw (S.mult ε ω) v)
            {x | (1 + (H : ℝ)) * ε ^ q < sameWalkExitDiscrepancy S r z ψ ε ω x} ≤
              ENNReal.ofReal (C * ε ^ (ν * (min a β - q / χ))) ∧
          (∫ x, sameWalkExitDiscrepancy S r z ψ ε ω x ∂srwLaw (S.mult ε ω) v) ≤
            C * (H : ℝ) *
              (if (χ : ℝ) < ν then ε ^ (min a β * χ)
               else if (χ : ℝ) = ν then ε ^ (min a β * ν) * (1 + |Real.log ε|)
               else ε ^ (min a β * ν))

/-- A pointwise bound gives the almost-everywhere one: `PointwiseSameWalkRatesStep` implies its successor. -/
theorem pointwiseSameWalkRatesAe_of_pointwise {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {E : ℝ → Set Ω} {ρ a β ν : ℝ}
    (h : PointwiseSameWalkRatesStep S E ρ a β ν) : PointwiseSameWalkRatesAeStep S E ρ a β ν := by
  intro r z hr hball ψ H χ hχ hχ1 hψ q hq hq' y hy
  obtain ⟨C, ε₀, hC, hε₀, hpt⟩ := h r z hr hball ψ H χ hχ hχ1 hψ q hq hq' y hy
  refine ⟨C, ε₀, hC, hε₀, fun ε hε hεs => ?_⟩
  exact Eventually.of_forall fun ω hω v hv => hpt ε hε hεs ω hω v hv

open Classical in
/-- The repaired exported same-walk statement, as an internal successor of the frozen
`CorrectedHarmonicSameWalkRateStmt` (`Draft/Section3HarmonicCorrected.lean`). The quenched clause is the
almost-everywhere implication `∀ᵐ ω ∂S.P, ω ∈ E ε → …`; everything else is identical to the frozen statement:
the exponents `bAnn, ν, κ`, the measurable event `E` with its polynomial complement, the sectionwise annealed
bound, and the three mean regimes with the factor `H`. -/
def CorrectedHarmonicSameWalkRateAeStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ bAnn : ℝ, 0 < bAnn ∧
  ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ν : ℝ, 0 < ν ∧
  ∀ a : ℝ, 0 < a → a < 2 / (2 + γ) ^ (2 : ℕ) → ∃ κ : ℝ, 0 < κ ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ E : ℝ → Set Ω, (∀ ε, MeasurableSet[S.envSigma] (E ε)) ∧
  ∃ CE εE : ℝ, 0 ≤ CE ∧ 0 < εE ∧
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
        ∀ᵐ ω ∂S.P, ω ∈ E ε →
          ∀ v ∈ interiorCellVertices ε (S.η ω) (ball z r),
            (srwLaw (S.mult ε ω) v)
              {x | (1 + (H : ℝ)) * ε ^ q < sameWalkExitDiscrepancy S r z ψ ε ω x} ≤
                ENNReal.ofReal (C * ε ^ (ν * (min a bAnn - q / χ))) ∧
            (∫ x, sameWalkExitDiscrepancy S r z ψ ε ω x ∂srwLaw (S.mult ε ω) v) ≤
              C * (H : ℝ) *
                (if (χ : ℝ) < ν then ε ^ (min a bAnn * χ)
                 else if (χ : ℝ) = ν then ε ^ (min a bAnn * ν) * (1 + |Real.log ε|)
                 else ε ^ (min a bAnn * ν))

end MatedCRT

#print axioms MatedCRT.pointwiseSameWalkRatesAe_of_pointwise
