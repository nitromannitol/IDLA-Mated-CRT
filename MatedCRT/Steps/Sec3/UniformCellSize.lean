import MatedCRT.Draft.Section2

/-! # Uniform exponent in the cell-size estimate -/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls
open scoped ENNReal

/-- The upper-cell bound with a probability exponent uniform over all valid
representations of the model. The corrected paper, Lemma 2.8 at line 669,
states polynomially high probability for its fixed model; this explicit
representation-uniform quantifier is a separate proof step. -/
def UniformCellSizeUpperStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ a : ℝ, 0 < a → a < 2 / (2 + γ) ^ 2 →
  ∃ κ : ℝ, 0 < κ ∧ ∀ (Ω : Type) [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      S.P {ω | ¬ ∀ i : ℤ, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
        diam (cell ε (S.η ω) i) ≤ ε ^ a} ≤ ENNReal.ofReal (C * ε ^ κ)

end MatedCRT
