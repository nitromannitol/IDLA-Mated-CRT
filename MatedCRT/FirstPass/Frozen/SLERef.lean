import MatedCRT.FirstPass.SLERef.Reference

/-!
# First pass: frozen external input for the reference law of whole-plane space-filling SLE (task fp-SLERef-reference-law)

`SLEReferenceExistsInput` is the frozen literature input that fixes the meaning of the abstract predicate
`SpaceFillingSLEModel.IsSLE` for the five cited numbered results (2.11, 2.14, 2.16, 2.18, 3.2). It is a proposition
about laws of curves. No Lean object constructs SLE here, and no Lean proof of the literature transfer is given.
Design: `notes/fp-gaps/CHATGPT-z2-sle-field-design.md` §2, §4, §8. The propositions it uses are in
`MatedCRT/FirstPass/SLERef/Reference.lean` and `MatedCRT/FirstPass/SLERef/Code.lean`.
-/

namespace MatedCRT

open MeasureTheory

/-- FIRST-PASS FROZEN. Reference existence and uniform literature transfer for whole-plane space-filling SLE.
PENDING TRUTH CHECK (operator): the truth of this proposition has not yet been checked by the operator.

The content: there is a family `ν : ℝ → Measure SLEPathCode` of rational-time code laws such that
(1) some space-filling SLE model `𝒮ref` has normalized law `ν` (`HasNormalizedSLELaw`) and is realized, for every
`γ ∈ (0, 2)`, by a valid environment on `ℝ` (`HasReferenceEnvironments`); and
(2) every space-filling SLE model `𝒮` with normalized law `ν` satisfies the five cited numbered results
(`SLECitedInputs 𝒮`: Theorem 2.11, Lemmas 2.14, 2.16, 2.18 and Lemma 3.2 of the paper).

The intended witness is the rooted, Lebesgue-area parametrized whole-plane space-filling SLE_κ from `∞` to `∞`, with
κ = 16/γ² > 4 for γ ∈ (0, 2) and time zero at the visit to the origin, realized by the canonical cone/SLE environments. The transfer argument is: a measurable normalized representative of the coupled curve has code law
`ν κ` (rational evaluation is a Borel isomorphism onto its image); its independence from the cone data is supplied by the
coupling; the quantum-area clock is recovered from the field and the normalized curve; the embedded graph is recovered
from the curve up to homeomorphism. The five cited statements then transfer uniformly from the reference environments.
This is a literature input stated as a proposition. It is NOT a Lean construction of SLE, and it does not identify the
law by any intrinsic characterization.

Sources: Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps* (arXiv:1807.07511v3), §2.1.3, printed pp. 17–18
(whole-plane imaginary-geometry construction and its Lebesgue-area parametrization); Duplantier–Miller–Sheffield,
*Liouville quantum gravity as a mating of trees* (arXiv:1409.7055v4), §1.4.1 with footnote 4 on printed p. 26 (chordal
to whole-plane passage), and Lemma 8.17 on printed p. 149 (quotient of proper continuous surjections with equal fibers).
The five cited statements carry their own locators in their Draft docstrings (Berestycki–Gwynne 2020 Theorem 1.2,
Lemmas 5.4 and 4.4, Proposition 5.1; Gwynne–Miller–Sheffield 2019 Theorem 3.9).

Used by: no firstPass_<sec>_<num> theorem yet; the consumer is `MatedCRT.exists_slecited_of_referenceExists`
(MatedCRT/FirstPass/SLERef.lean). -/
def SLEReferenceExistsInput : Prop :=
  ∃ ν : ℝ → Measure SLEPathCode, SLEReferenceInput ν

end MatedCRT
