import Mathlib.MeasureTheory.Measure.Regular

/-! # FIRST PASS Frozen statements for S2k (task fp-S2k-closure-inside)

Each `def` below is an EXTERNAL general-measure-theory fact used as an explicit hypothesis. Nothing here is about this
paper's clusters, odometers, harmonic balls or IDLA processes. -/

namespace MatedCRT.FirstPass.S2k

open MeasureTheory

/-- FIRST-PASS FROZEN. Lusin's theorem for finite Borel measures on complete separable metric spaces, in the form
used by the Borel full-law transfer (cycle note section 3.1). For a finite Borel measure `P` on a complete separable
metric space `X`, a Borel map `F` into a separable metric space `Y`, and every `ε > 0`, there is a compact `K ⊆ X`
with `P Kᶜ < ε` such that `F|K` is continuous. Source: Kechris, *Classical Descriptive Set Theory* (1995), Theorem 17.11
(tightness of Borel measures on Polish spaces, p. 107) and Theorem 17.12 (Lusin's theorem, p. 108). Locator taken from
`notes/fp-gaps/CHATGPT-closure-inside-cycle.md` section 2; the printed page is not verified by this file.
Used by: firstPass_exists_borel_image_fullLaw (`S2k/BorelTransfer.lean`). -/
def FrozenLusinCompactContinuity : Prop :=
  ∀ (X Y : Type) [MetricSpace X] [CompleteSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
    (P : Measure X) [IsFiniteMeasure P] (F : X → Y), Measurable F →
    ∀ ε : ENNReal, 0 < ε → ∃ K : Set X, IsCompact K ∧ P Kᶜ < ε ∧ ContinuousOn F K

end MatedCRT.FirstPass.S2k
