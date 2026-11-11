import MatedCRT.LPStaging.Prob.CauchyInProbabilitySubseq

/-!
# Identification of the limit clock: Borel-Cantelli transfer from a product measure

Let `P` be a measure on `Ω`, `Q` a measure on `Z`, and `ψ : Ω → Y` measurable. The image `M` of `P ⊗ Q` under
`(ω, b) ↦ (ψ ω, b)` is the joint law of the field and the path. If the events `{ofReal ((1/2)^k) < D k}` have `M`-mass at
most `ofReal ((1/2)^k)`, the first Borel-Cantelli lemma (`LatticeProb.ae_eventually_le_of_prob_le`) gives `M`-almost
every point eventually below the level, and Fubini for the product measure (`Measure.ae_ae_of_ae_prod`) gives the
statement for `P`-almost every `ω` and `Q`-almost every `b`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- Borel-Cantelli transfer from the image `((P ⊗ Q).map fun p ↦ (ψ p.1, p.2))` of a product measure: if the
`k`-th events have mass at most `(1/2)^k`, then for `P`-almost every `ω` and `Q`-almost every `b`, `D k (ψ ω, b)`
is eventually at most `(1/2)^k`. -/
theorem ae_ae_eventually_le_of_map_prob_le {Ω Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [MeasurableSpace Z] (P : Measure Ω) (Q : Measure Z) [SFinite Q] (ψ : Ω → Y) (hψ : Measurable ψ)
    (D : ℕ → Y × Z → ℝ≥0∞)
    (hD : ∀ k, ((P.prod Q).map fun p : Ω × Z => (ψ p.1, p.2)) {x | ENNReal.ofReal ((1 / 2) ^ k) < D k x}
        ≤ ENNReal.ofReal ((1 / 2) ^ k)) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂Q, ∀ᶠ k in atTop, D k (ψ ω, b) ≤ ENNReal.ofReal ((1 / 2) ^ k) := by
  have hf : Measurable fun p : Ω × Z => (ψ p.1, p.2) :=
    (hψ.comp measurable_fst).prodMk measurable_snd
  have h1 : ∀ᵐ x ∂((P.prod Q).map fun p : Ω × Z => (ψ p.1, p.2)),
      ∀ᶠ k in atTop, D k x ≤ ENNReal.ofReal ((1 / 2) ^ k) :=
    LatticeProb.ae_eventually_le_of_prob_le _ D hD
  have h2 : ∀ᵐ p ∂(P.prod Q), ∀ᶠ k in atTop, D k (ψ p.1, p.2) ≤ ENNReal.ofReal ((1 / 2) ^ k) :=
    ae_of_ae_map hf.aemeasurable h1
  exact Measure.ae_ae_of_ae_prod h2

end MatedCRT.KilledOccupation

#print axioms MatedCRT.KilledOccupation.ae_ae_eventually_le_of_map_prob_le
