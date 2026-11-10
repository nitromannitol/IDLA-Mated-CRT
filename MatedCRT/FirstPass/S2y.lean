import MatedCRT.FirstPass.S2z
import MatedCRT.FirstPass.S2j

/-! # Closure gap G9: the coded Lemma 2.6 from the printed Lemma 2.6 (FirstPass S2y, z8, fp-S2y-G9-closed)

Closure gap G9 (z1; needed by `firstPass_5_3_final`, FirstPass/S5c/FinalSurplus.lean:229, as `hLs`): the coded form
`ConeScaleInvarianceCodedStmt` (FirstPass/S2g/LawCoded.lean:20) is obtained from the Draft statement
`ConeScaleInvarianceStmt` (Draft/Section2.lean:108). The almost sure measurability of the stopped cone families is
`coneFamilyAEMeasurable_proved` (FirstPass/S2j.lean:28), and the stopped route is
`coneScaleInvarianceCoded_of_stmt_stopped` (FirstPass/S2z.lean:64).

The two code chains are kept apart: the coded law uses the `MatedCRT.processCode`, `MatedCRT.globalCode` of
FirstPass/S2g/LawCode.lean; the measurability chain of FirstPass/S2j.lean uses the renamed copies
`processCodeTimed`, `measurable_processCodeTimed`, `globalCodeFactor` of FirstPass/S2i/ProcessCode.lean and
FirstPass/S2i/GlobalFactor.lean.

Hypotheses of `coneScaleInvarianceCoded_of_stmt`, with their classes:
* `hStmt : ConeScaleInvarianceStmt`: Draft, Lemma 2.6 (Draft/Section2.lean:108).
* `h24 : ConeHarmonicBallsUpToFixedTimeStmt`: Draft, Lemma 2.4 in the printed T' = T form (Draft/Section2.lean:66).
  It is kept in the Draft form, because `coneScaleInvarianceCoded_of_stmt_stopped` takes this form and not the corrected
  form `ConeHarmonicBallsUpToFixedTimeCorrectedStmt` (FirstPass/S2b.lean:43).
* `h25 : ConeScaleInvarianceUpToFixedTimeStmt`: Draft, Lemma 2.5 (Draft/Section2.lean:88).
* `hcan : ConeCanonicalHalfBallStep`: Step (FirstPass/S2g.lean:82), checked TRUE (CHATGPT-q1-open-steps.md §3).
* `hcl : ConeHalfBallClosureInsideStep`: Step (Proofs/Sec2/ConeFamilyMeasurable/StoppedClosure.lean:18), checked TRUE
  (CHATGPT-closure-inside-cycle.md §4).
* `h27 : VolumeGrowthStmt`: Draft (Draft/Section2.lean:121).
* `hE1 : ConeCircleLawUniqueStep`: frozen Step (FirstPass/Frozen/S2i.lean:27), checked TRUE (chat 180 §3).
* `hE2 : ConeReferenceExistsStep`: frozen Step (FirstPass/Frozen/S2i.lean:46), checked TRUE (chat 180 §3).
* `hscale : QuantumConeScalingInput`: literature input (External/QuantumCone.lean:19; DMS14 Proposition 4.13(i)).
* `h22 : LQGMeasurePropertiesStmt`: Draft, Fact 2.2 (Draft/Section2.lean:39).
-/

namespace MatedCRT.FirstPassG9Closed

/-- **Closure gap G9 (z8, fp-S2y-G9-closed).** The coded law of Lemma 2.6 (`ConeScaleInvarianceCodedStmt`) follows from
the printed Lemma 2.6 (`ConeScaleInvarianceStmt`) and the hypotheses listed in the file header. The measurability of the
stopped cone families is supplied by `coneFamilyAEMeasurable_proved` from the Steps `hcan` and `hcl` and the frozen
Steps `hE1` and `hE2`; the stopped route `coneScaleInvarianceCoded_of_stmt_stopped` then gives the coded form. -/
theorem coneScaleInvarianceCoded_of_stmt
    (hStmt : ConeScaleInvarianceStmt) (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (h25 : ConeScaleInvarianceUpToFixedTimeStmt)
    (hcan : ConeCanonicalHalfBallStep) (hcl : ConeHalfBallClosureInsideStep) (h27 : VolumeGrowthStmt)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt) :
    ConeScaleInvarianceCodedStmt :=
  MatedCRT.FirstPassG9.coneScaleInvarianceCoded_of_stmt_stopped hStmt h24 h25
    (coneFamilyAEMeasurable_proved hcan hcl h27 hE1 hE2 hscale h22) hscale

end MatedCRT.FirstPassG9Closed

#print axioms MatedCRT.FirstPassG9Closed.coneScaleInvarianceCoded_of_stmt
