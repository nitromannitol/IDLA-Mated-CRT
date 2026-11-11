import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Core

/-!
# Borel-set form of the Lemma 2.9 event (fp-S7y-h29-measurable, measurable-binder copies)

`CountingAtMeas` is `ConstantOrderDiv.CountingAt` (MatedCRT/Proofs/Sec6/ConstantOrderLowerBoundDiv/Core.lean:45) with
`MeasurableSet D` added before `D ⊆ ball 0 ρ`, the form that BG20 Lemma A.4 states. The measurable-binder copies of the
Lemma 6.8 chain (`S7y/Vertex.lean`, `S7y/OfSteps.lean`, `S7y/Final.lean`) take this predicate in place of `CountingAt`.
No original declaration is edited.
-/

namespace MatedCRT

open MeasureTheory Set Metric

namespace ConstantOrderDiv

/-- The conclusion of Lemma 2.9 at `ε` for Borel `D` (the event of `CountingMeasureConvergenceMeasurableStmt`). -/
def CountingAtMeas (ε : ℝ) (η : ℝ → ℂ) (μ : Measure ℂ) (ρ α₉ β₉ : ℝ) : Prop :=
  ∀ (D : Set ℂ) (f : ℂ → ℝ) (w : ℤ → ℂ), MeasurableSet D → D ⊆ ball 0 ρ →
    (∀ x ∈ thickening (ε ^ α₉) D, 0 ≤ f x ∧ |f x| ≤ ε ^ (-β₉)) →
    (∀ x ∈ thickening (ε ^ α₉) D, ∀ y ∈ thickening (ε ^ α₉) D, |f x - f y| ≤ ε ^ (-β₉) * ‖x - y‖) →
    (∀ k ∈ cellVertices ε η D, w k ∈ cell ε η k ∩ closure D) →
    ε⁻¹ * ∫ x in D, f x ∂μ - ε ^ (-1 + α₉) ≤ ∑' k : cellVertices ε η D, f (w k) ∧
    ∑' k : cellVertices ε η D, f (w k) ≤ ε⁻¹ * ∫ x in thickening (ε ^ α₉) D, f x ∂μ + ε ^ (-1 + α₉)

end ConstantOrderDiv

end MatedCRT
