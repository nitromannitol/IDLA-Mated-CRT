import MatedCRT.FirstPass.S5S6S7

/-!
# Closed results, Section 7 (task fp-Closure-counted-results, worker z1)

Closed: 7.2 (`closed_7_2`, corrected form), 7.3 (`closed_7_3`). Not closed: 7.1 (needs Lemma 2.3 and Lemma 4.1).
See the report.
-/

namespace MatedCRT

/-- Lemma 7.2 (mass bound for the odometer above scale), closed in the corrected form. Hypotheses: cited Lemmas
2.16 and 2.8. -/
alias closed_7_2 := firstPass_7_2_corrected

/-- Lemma 7.3 (odometer bound by mass), closed. No hypotheses beyond `𝒮`. -/
alias closed_7_3 := firstPass_7_3

end MatedCRT
