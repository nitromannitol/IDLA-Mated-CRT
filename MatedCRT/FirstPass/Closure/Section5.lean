import MatedCRT.FirstPass.S5S6S7

/-!
# Closed results, Section 5 (task fp-Closure-counted-results, worker z1)

Closed: 5.2 (`closed_5_2`), 5.4 (`closed_5_4`). Not closed: 5.3 (needs Lemma 4.1, which is blocked, and the coded form
`ConeScaleInvarianceCodedStmt` of Lemma 2.6), 5.1 is not in the counted set. See the report.
-/

namespace MatedCRT

/-- Lemma 5.2 (general IDLA lower bound), closed. Hypotheses: `VolumeGrowthStmt`, `CellSizeEstimateStmt 𝒮` (cited). -/
alias closed_5_2 := firstPass_5_2

/-- Lemma 5.4 (L lower bound), closed. Hypotheses: cited Green function and counting-measure statements. -/
alias closed_5_4 := firstPass_5_4

end MatedCRT
