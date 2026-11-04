import MatedCRT.Proofs.Sec6.GoodAnnulusPrevalence.Locality
import MatedCRT.Proofs.Sec6.AnnulusHit.Main
import MatedCRT.Proofs.Field.LawTransferComplete

/-!
# Lemma 6.4 (lemma:good-prevalance, line 2335; event corrected by [C5])

The proof (lines 2404-2417) is `goodAnnulusPrevalence_of_steps` (`MatedCRT/Steps/Sec6/GoodAnnulusPrevalence.lean`).
Its inputs are now:
* Lemma 6.6 (`AnnulusIterateStmt`): proved, `annulusIterate` (`MatedCRT/Proofs/Field/LawTransferComplete.lean`);
* the transfer of Lemma 6.6 to the cone field (IR-c4-5): proved from eq:gff on mean-zero pairings,
  `annulusIterateConeTransfer` (`ConeMeanZeroRestrictionStep`);
* the locality of `E_r(z)` modulo additive constant (IR-c4-6): proved from the determination of circle-average
  differences by the field modulo additive constant, `goodAnnulusEventLocality` (`CircleAverageModConstStep`);
* Lemma 6.5 (`AnnulusHitStmt`): `annulusHit_of_volumeTail` (`MatedCRT/Proofs/Sec6/AnnulusHit/Main.lean`).

Remaining inputs of Lemma 6.4: those of Lemma 6.5 and the two field steps `ConeMeanZeroRestrictionStep`
(eq:gff, line 444) and `CircleAverageModConstStep`.
-/

namespace MatedCRT

/-- **Lemma 6.4** (lemma:good-prevalance, line 2335) from Lemma 6.5 and the two field steps of its proof (eq:gff on
mean-zero pairings and the determination of circle-average differences modulo additive constant). Lemma 6.6 is
`annulusIterate`. -/
theorem goodAnnulusPrevalence_of_annulusHit (h65 : AnnulusHitStmt) (hR : ConeMeanZeroRestrictionStep)
    (hD : CircleAverageModConstStep) : GoodAnnulusPrevalenceStmt :=
  goodAnnulusPrevalence_of_fieldSteps annulusIterate h65 hR hD

/-- **Lemma 6.4** (lemma:good-prevalance, line 2335) from the field inputs of Lemmas 6.4 and 6.5 only. -/
theorem goodAnnulusPrevalence_of_fieldInputs (h0 : WholePlaneLQGExistenceStep)
    (h1 : ConeWholePlaneWeylComparisonStep) (h2 : WholePlaneLQGCoordinateChangeStep)
    (hV : WholePlaneUpperVolumeTailStep) (hR : ConeMeanZeroRestrictionStep) (hD : CircleAverageModConstStep) :
    GoodAnnulusPrevalenceStmt :=
  goodAnnulusPrevalence_of_annulusHit (annulusHit_of_volumeTail h0 h1 h2 hV) hR hD

end MatedCRT
