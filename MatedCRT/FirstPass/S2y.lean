import MatedCRT.FirstPass.S2z

/-! # Closure gap G9: the coded Lemma 2.6 from the printed Lemma 2.6 (FirstPass S2y, z8, fp-S2y-G9-closed). PARTIAL.

STATUS: G9 is NOT closed in this file. The stopped route is `coneScaleInvarianceCoded_of_stmt_stopped`
(FirstPass/S2z.lean:64). Its measurability input `hfam : ConeFamilyAEMeasurableStep` (Steps/Sec2/ConeHarmonicBalls.lean:31)
is kept here as an explicit hypothesis. The intended discharge is
`coneFamilyAEMeasurable_proved hcan hcl h27 hE1 hE2 hscale h22` (FirstPass/S2j.lean:28). It cannot be imported in the same
file as FirstPass/S2z.lean: `MatedCRT.processCode`, `MatedCRT.globalCode` and `MatedCRT.measurable_processCode` are declared
both in FirstPass/S2g/LawCode.lean (lines 30, 34, 44) and in FirstPass/S2i/ProcessCode.lean:20,108 and
FirstPass/S2i/GlobalFactor.lean:234. Lean rejects the import (`environment already contains 'MatedCRT.processCode'`).
Once one of the two chains is renamed, replace `hfam` by the discharge above.
-/

namespace MatedCRT.FirstPassG9Closed

/-- **Closure gap G9 (z8, partial).** The coded law of Lemma 2.6 from the printed Lemma 2.6, given the stopped
measurability step `hfam`. Hypotheses: `hStmt` Draft Lemma 2.6 (Draft/Section2.lean:108); `h24` Draft Lemma 2.4 in the
printed T' = T form (Draft/Section2.lean:66); `h25` Draft Lemma 2.5 (Draft/Section2.lean:88); `hfam` Step, open here
(see the file header); `hscale` literature input (External/QuantumCone.lean:19). -/
theorem coneScaleInvarianceCoded_of_stmt
    (hStmt : ConeScaleInvarianceStmt) (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (h25 : ConeScaleInvarianceUpToFixedTimeStmt) (hfam : ConeFamilyAEMeasurableStep)
    (hscale : QuantumConeScalingInput) :
    ConeScaleInvarianceCodedStmt :=
  MatedCRT.FirstPassG9.coneScaleInvarianceCoded_of_stmt_stopped hStmt h24 h25 hfam hscale

end MatedCRT.FirstPassG9Closed

#print axioms MatedCRT.FirstPassG9Closed.coneScaleInvarianceCoded_of_stmt
