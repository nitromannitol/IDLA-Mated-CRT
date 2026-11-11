import MatedCRT.FirstPass.S5qe
import MatedCRT.FirstPass.S4S6c.HoneModelInputs68
import MatedCRT.FirstPass.S4S6c.CountingExitAlpha68

/-!
# The counting exponent at the exit exponent from the core certified model

The first-pass producer `CountingExitAlpha68.countingAtExitAlphaStmt_of_firstPass` (CountingExitAlpha68.lean:152)
takes the full certified reference model `CertifiedReferenceModel ν 𝒮` (FirstPass/SLERef/Certified.lean:54). It uses
two of its conjuncts only: the counting measure convergence (conjunct 6) and the exit-time upper bound (conjunct 14).
Both are among the seventeen conjuncts that `CertifiedReferenceModelCore ν 𝒮` (FirstPass/S5qe.lean:33) keeps, so the
core model suffices. The frozen conjunct 17, `FrozenTruncatedQuenchedLawsFixedTime 𝒮`, is neither used nor added.

The core argument is the same as the first-pass one, fed by the core projections
`HoneModelInputs68.countingMeasure_of_core` (HoneModelInputs68.lean:112) and
`CertifiedReferenceModelCore.exitTimeUpperBound` (S5qe.lean:86).
-/

open MeasureTheory

namespace MatedCRT
namespace CountingExitAlphaCore68

/-- **Counting exponent at the exit exponent from the core certified model.** The
one-exponent counting statement `CountingAtExitAlphaStmt 𝒮` (Guard68S10.lean:937), from the core certified reference
model `CertifiedReferenceModelCore ν 𝒮`. The proof is that of `countingAtExitAlphaStmt_of_firstPass`
(CountingExitAlpha68.lean:152), with the core projections in place of the full-model ones. -/
theorem countingAtExitAlphaStmt_of_core {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (h : CertifiedReferenceModelCore ν 𝒮) : Lemma68Guard10.CountingAtExitAlphaStmt 𝒮 :=
  CountingExitAlpha68.countingAtExitAlphaStmt_of_counting_exit
    (HoneModelInputs68.countingMeasure_of_core h) (CertifiedReferenceModelCore.exitTimeUpperBound h)

end CountingExitAlphaCore68
end MatedCRT

#print axioms MatedCRT.CountingExitAlphaCore68.countingAtExitAlphaStmt_of_core
