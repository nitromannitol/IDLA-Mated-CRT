import MatedCRT.FirstPass.Derived.ZeroConeLemmaA1Proof
import MatedCRT.FirstPass.Derived.ZeroConeLemmaA1GFFTail

/-!
# Lemma A.1 of Gwynne–Miller–Sheffield for the circle-average zero cone, from Lemma A.4

The tail at infinity of the whole-plane GFF modulo constants is trivial (`wholePlaneGFFExteriorTailTrivial`, by
inversion and the germ 0-1 law at the origin), so Lemma A.1 for the circle-average embedding of the `0`-quantum cone
(`ZeroConeCircleAverageLemmaA1`) follows from Lemma A.4 alone (`zeroConeCircleAverageLemmaA1_of_lemmaA4`).
-/

set_option autoImplicit false

open Set

namespace MatedCRT

/-- **Lemma A.1 of Gwynne–Miller–Sheffield for the circle-average zero cone, from Lemma A.4.** -/
theorem zeroConeCircleAverageLemmaA1_of_lemmaA4 (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hA4 : ZeroConeUniformRootLemmaA4 γ hγ) : ZeroConeCircleAverageLemmaA1 γ hγ :=
  zeroConeCircleAverageLemmaA1_of_lemmaA4_of_tail wholePlaneGFFExteriorTailTrivial γ hγ hA4

end MatedCRT
