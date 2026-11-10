import MatedCRT.FirstPass.S1S2S8SA
import MatedCRT.FirstPass.S2g.Assembly2456

/-!
# Closed results, Section 2 (task fp-Closure-counted-results, worker z1)

Closed: 2.4 (`closed_2_4`), 2.5 (`closed_2_5`), 2.6 (`closed_2_6`), 2.13 (`closed_2_13`), 2.17 (`closed_2_17`),
2.19 (`closed_2_19`). The aliases keep only FIRST-PASS FROZEN Props, External Props, cited results (Draft
2.2, 2.7, 2.8, 2.11, 2.15, 2.16, 2.18) and the other paper's harmonic-balls statements (Thm 1.1, Thm 5.5,
Lemma 3.2 and the cluster lemmas of Harmonic-Balls-LQG). No paper-owned Draft statement is a hypothesis.

Not closed here: 2.3 (`firstPass_2_3` needs the Draft `ConeHarmonicBallsUpToFixedTimeStmt` and
`ConeScaleInvarianceUpToFixedTimeStmt`, see the gap list in the report).
Conclusions: `closed_2_4` and `closed_2_5` conclude the S2g canonical statements, not the printed Draft statements.
-/

namespace MatedCRT

/-- Lemma 2.4 (existence up to fixed time), closed in the S2g form. Conclusion
`ConeHarmonicBallsUpToFixedTimeCanonicalStmt`. -/
alias closed_2_4 := firstPass_2_4_corrected

/-- Lemma 2.5 (scale invariance up to fixed time), closed in the S2g canonical form. -/
alias closed_2_5 := firstPass_2_5_corrected

/-- Lemma 2.6 (scale invariance), closed. Conclusion `ConeScaleInvarianceStmt`. -/
alias closed_2_6 := firstPass_2_6_corrected

/-- Lemma 2.13 (maximum principle), closed. Hypothesis: `FrozenAdjacentCellsMeetAe 𝒮`. -/
alias closed_2_13 := firstPass_2_13

/-- Lemma 2.17 (bounded exit time), closed. Hypothesis: `VolumeGrowthStmt` (cited, Lemma 2.7). -/
alias closed_2_17 := firstPass_2_17

/-- Lemma 2.19 (expected exit time, explicit bound), closed. The paper-owned input `BoundedExitTimeRVStmt`
(Lemma 2.17) is discharged by `closed_2_17`; the remaining input `ExitTimeUpperBoundStmt 𝒮` is cited (Lemma 2.18). -/
theorem closed_2_19 {𝒮 : SpaceFillingSLEModel} (h27 : VolumeGrowthStmt)
    (h18 : ExitTimeUpperBoundStmt 𝒮) : ExpectedExitTimeExplicitBoundStmt 𝒮 :=
  firstPass_2_19 (h17 := closed_2_17 h27) (h18 := h18)

end MatedCRT
