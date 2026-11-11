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

Hypotheses of Lemma 6.4: those of Lemma 6.5 and the field step `ConeMeanZeroRestrictionStep`
(eq:gff, line 444). `CircleAverageModConstStep` is proved by `circleAverageModConstStep`
(`MatedCRT/Proofs/Field/ConeCircleModConst.lean:367`) and passed as `hD`.
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

/-! ## Final forms

The hypotheses below are exactly the steps of the proofs of Lemmas 6.5 and 6.4 that are named steps (see docs/campaign/COUNTED.md). Every
proved ingredient is discharged: Lemma 6.6 (`annulusIterate`), the transfer of Lemma 6.6 to the cone field
(`annulusIterateConeTransfer`, IR-c4-5), the locality of `E_r(z)` modulo additive constant (`goodAnnulusEventLocality`,
IR-c4-6) and the tightness step of Lemma 6.5 (`wholePlaneGoodAnnulusTightness_of_volumeTail`, IR-c4-4). Lemma 6.5 uses
no cited Draft statement and no External input. -/

/-- **Lemma 6.5, final form** (lemma:annulus-hit, line 2350; event corrected by [C5]). Hypotheses, all named steps
(`MatedCRT/Steps/Sec6/AnnulusHit.lean`):
* `WholePlaneLQGExistenceStep` (IR-c4-1): a whole-plane GFF with its `γ`-LQG measure exists;
* `ConeWholePlaneWeylComparisonStep` (IR-c4-2): eq:gff (line 444) with Weyl scaling, near an admissible annulus;
* `WholePlaneLQGCoordinateChangeStep` (IR-c4-3): eq:gff-scaling and the LQG coordinate change for `h^ℂ`;
* `WholePlaneUpperVolumeTailStep` (literature content of IR-c4-4): uniform upper volume bound for `μ_{h^ℂ}` with
  polynomially high probability. -/
theorem annulusHit_final (h0 : WholePlaneLQGExistenceStep) (h1 : ConeWholePlaneWeylComparisonStep)
    (h2 : WholePlaneLQGCoordinateChangeStep) (hV : WholePlaneUpperVolumeTailStep) : AnnulusHitStmt :=
  annulusHit_of_volumeTail h0 h1 h2 hV

/-- **Lemma 6.4, final form** (lemma:good-prevalance, line 2335; event corrected by [C5]). Hypotheses, all named steps
(see docs/campaign/COUNTED.md): the four of Lemma 6.5 (`annulusHit_final`) and
* `ConeMeanZeroRestrictionStep` (eq:gff on the mean-zero pairings, line 444; input of IR-c4-5,
  `MatedCRT/Steps/Sec6/GoodAnnulusPrevalence.lean`);
* `CircleAverageModConstStep` (circle-average differences are determined by the field modulo additive constant; input
  of IR-c4-6, same file; proved as `circleAverageModConstStep`, `MatedCRT/Proofs/Field/ConeCircleModConst.lean:367`,
  and passed here as `hD`). -/
theorem goodAnnulusPrevalence_final (h0 : WholePlaneLQGExistenceStep) (h1 : ConeWholePlaneWeylComparisonStep)
    (h2 : WholePlaneLQGCoordinateChangeStep) (hV : WholePlaneUpperVolumeTailStep)
    (hR : ConeMeanZeroRestrictionStep) (hD : CircleAverageModConstStep) : GoodAnnulusPrevalenceStmt :=
  goodAnnulusPrevalence_of_annulusHit (annulusHit_final h0 h1 h2 hV) hR hD

end MatedCRT
