import MatedCRT.FirstPass.S6r.ShortWindow
import MatedCRT.FirstPass.S6q
import MatedCRT.Proofs.Sec6.GoodAnnulusPrevalence.ConeTransfer
import MatedCRT.Proofs.Sec6.GoodAnnulusPrevalence.Locality
import MatedCRT.Proofs.Field.ConeCircleModConst

/-!
# PRO step 3 (short-window good-radius prevalence): the closed form

`shortWindow_prevalence` (ShortWindow.lean:297) takes three inputs `h65`, `hT`, `hL`. This file discharges each of
them from the proved results where a provider exists, and keeps the rest as named hypotheses with their exact types:

* `hL : GoodAnnulusEventLocalityStep` is proved: `MatedCRT.goodAnnulusEventLocality` (Locality.lean:200) applied to
  the proved step `MatedCRT.Field.ConeCircle.circleAverageModConstStep` (ConeCircleModConst.lean:367).
* `hT : AnnulusIterateConeTransferStep` is `MatedCRT.annulusIterateConeTransfer` (ConeTransfer.lean:74) applied to the
  named step `ConeMeanZeroRestrictionStep` (eq:gff, line 444; IR-A3). No provider exists in the tree.
* `h65 : FirstPass64.AnnulusHitUniformStmt` is `FirstPass64.firstPass_6_5_uniform` (S6q.lean:26) applied to the named
  steps `WholePlaneLQGExistenceStep` (Duplantier-Sheffield 2011, Proposition 1.1; IR-c4-1),
  `WholePlaneLQGCoordinateChangeStep` (eq:gff-scaling; IR-c4-3) and `WholePlaneUpperVolumeTailStep` (Rhodes-Vargas 2014,
  Theorem 2.6; IR-c4-4). The coordinate-change step is stated for the dyadic predicate `IsLQGMeasure` of Harmonic-Balls;
  its proved counterpart `WholePlaneLQGCoordinateChangeStepCont` (Proofs/Field/WholePlaneLQGCont.lean:86) is for the
  all-scales predicate `IsLQGMeasureCont` (eq:measure-lim), and no dyadic-to-all-scales bridge is in the tree.
-/

namespace MatedCRT.Lemma68Window

/-- **Locality of the good annulus event** (`GoodAnnulusEventLocalityStep`, lines 2388-2390), proved: `E_r(z)` is a.s.
determined by the field on `𝔸_{r/3,3r}(z)` modulo additive constant, from the proved circle-average step. -/
theorem shortWindow_hL_proved : GoodAnnulusEventLocalityStep :=
  MatedCRT.goodAnnulusEventLocality MatedCRT.Field.ConeCircle.circleAverageModConstStep

/-- **Cone transfer of the annulus iteration** (`AnnulusIterateConeTransferStep`, IR-c4-5), from the mean-zero
restriction `ConeMeanZeroRestrictionStep` (eq:gff on the mean-zero pairings, line 444). -/
theorem shortWindow_hT_of_meanZero (hR : ConeMeanZeroRestrictionStep) : AnnulusIterateConeTransferStep :=
  MatedCRT.annulusIterateConeTransfer hR

/-- **One-annulus hit bound** (`FirstPass64.AnnulusHitUniformStmt`, Lemma 6.5 with `C = C(p)`), from the three
whole-plane inputs of `firstPass_6_5_uniform`: existence of the whole-plane LQG measure, the LQG coordinate change and
the upper volume tail. The cone Weyl comparison of Step 1 is proved (`AnnulusHitField.coneWholePlaneWeylComparison`). -/
theorem shortWindow_h65_of_steps (h0 : WholePlaneLQGExistenceStep) (h2 : WholePlaneLQGCoordinateChangeStep)
    (hV : WholePlaneUpperVolumeTailStep) : MatedCRT.FirstPass64.AnnulusHitUniformStmt :=
  MatedCRT.FirstPass64.firstPass_6_5_uniform h0 h2 hV

/-- **PRO step 3, `ShortWindowGoodRadiusPrevalenceStmt`, with the inputs of `shortWindow_prevalence` discharged where
proved.** The named hypotheses that remain are the whole-plane LQG existence `h0`, the whole-plane LQG coordinate change
`h2`, the whole-plane upper volume tail `hV` and the cone mean-zero restriction `hR`; the locality input is proved. -/
theorem shortWindowGoodRadiusPrevalence_closed (h0 : WholePlaneLQGExistenceStep)
    (h2 : WholePlaneLQGCoordinateChangeStep) (hV : WholePlaneUpperVolumeTailStep)
    (hR : ConeMeanZeroRestrictionStep) : ShortWindowGoodRadiusPrevalenceStmt :=
  shortWindow_prevalence (shortWindow_h65_of_steps h0 h2 hV) (shortWindow_hT_of_meanZero hR)
    shortWindow_hL_proved

end MatedCRT.Lemma68Window
