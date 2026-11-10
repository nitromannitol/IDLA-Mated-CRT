import MatedCRT.FirstPass.S5S6S7

/-!
# Closed results, Section 6 (task fp-Closure-counted-results, worker z1)

Closed: 6.4 (`closed_6_4`, good annulus prevalence), 6.5 (`closed_6_5`, annulus hit), 6.10 (`closed_6_10`, iterative bound).
Not closed: 6.1 (needs Lemma 5.1, not counted), 6.7, 6.8, 6.9 excluded from the counted set. See the report.
-/

namespace MatedCRT

/-- Lemma 6.4 (good prevalence of annuli), closed. Hypotheses: frozen whole-plane Props. -/
alias closed_6_4 := firstPass_6_4

/-- Lemma 6.5 (annulus hit), closed. Hypotheses: frozen whole-plane Props. -/
alias closed_6_5 := firstPass_6_5

/-- Lemma 6.10 (iterative bound), closed. Hypotheses: cited Lemmas 2.7, 2.8, 2.9, 2.18 and frozen whole-plane Props. -/
alias closed_6_10 := firstPass_6_10

end MatedCRT
