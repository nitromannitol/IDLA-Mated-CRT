import MatedCRT.Proposed.GwynneMillerSheffield
import MatedCRT.Draft.Section2

/-! # Pointwise environment event for cell and annulus estimates -/

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal

/-- An environment-measurable event satisfying both geometric conditions
almost everywhere at each mesh, with a polynomial exceptional bound.
The parameters must be chosen using the cell and annulus estimates; the
predicate is not asserted for arbitrary parameters. -/
def PointwiseCellAnnulusEnvelopeStep {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (ρ a β p κ : ℝ) : Prop :=
  ∃ E : ℝ → Set Ω, (∀ ε, MeasurableSet[S.envSigma] (E ε)) ∧
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      S.P (E ε)ᶜ ≤ ENNReal.ofReal (C * ε ^ κ) ∧
      ∀ᵐ ω ∂S.P, ω ∈ E ε →
        (∀ i : ℤ, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
          diam (cell ε (S.η ω) i) ≤ ε ^ a) ∧
        (∀ z ∈ ball (0 : ℂ) ρ, ∀ s : ℝ, ε ^ β ≤ s → s ≤ ρ →
          ball z (2 * s) ⊆ ball 0 ρ → ∀ j ∈ cellVertices ε (S.η ω) (ball z s),
          ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) j
            {path | ∀ y ∈ cellVertices ε (S.η ω) (sphere z (s / 2)),
              walkDisconnectsBeforeHit (S.mult ε ω)
                (cellVertices ε (S.η ω) (sphere z (2 * s))) y path})

end MatedCRT
