import MatedCRT.FirstPass.S6r.ShortWindowClosed
import MatedCRT.FirstPass.Frozen.S5S6S7

/-!
# hprev of the short-window good-radius prevalence, whole-plane inputs frozen

`shortWindowGoodRadiusPrevalence_closed` (ShortWindowClosed.lean, `MatedCRT.Lemma68Window`) proves
`ShortWindowGoodRadiusPrevalenceStmt` from four named inputs: `h0 : WholePlaneLQGExistenceStep`,
`h2 : WholePlaneLQGCoordinateChangeStep`, `hV : WholePlaneUpperVolumeTailStep` and `hR : ConeMeanZeroRestrictionStep`.

This file discharges `h0` and `hV` by the first-pass frozen external inputs and keeps `h2` and `hR` as named hypotheses.

* `h0` is `FPWholePlaneLQGExistence` (Frozen/S5S6S7.lean, `MatedCRT.FPWholePlaneLQGExistence`): the whole-plane GFF with its
  `γ`-LQG measure, Duplantier-Sheffield 2011, Proposition 1.1. The staged HB Prop `LQGMeasureExistence`
  (HarmonicBalls/Proposed/LQG.lean, line 68) does NOT match it: that Prop is conditional on a given whole-plane GFF
  (`IsWholePlaneGFF P hC hcirc → …`) and concludes `IsLQGMeasureOfField P γ α₀ hcirc μ`, while `WholePlaneLQGExistenceStep`
  also needs a probability space carrying a whole-plane GFF. The missing piece is the GFF existence
  `WholePlaneGFFExistsFrozen` (HarmonicBalls/FirstPass/S11r/Frozen.lean, line 39), which is not on the approved list.
* `hV` is `FPWholePlaneUpperVolumeTail` (Frozen/S5S6S7.lean): the uniform upper volume bound for the whole-plane LQG
  measure, Rhodes-Vargas 2014, Theorem 2.6.

No new frozen Prop is introduced here: both frozen inputs already exist in the frozen layer with the statements of the
named steps.
-/

namespace MatedCRT.Lemma68Window

/-- **hprev of the short-window good-radius prevalence, with the whole-plane inputs frozen.** The conclusion of
`shortWindowGoodRadiusPrevalence_closed` with `h0` and `hV` supplied by the frozen Props `FPWholePlaneLQGExistence`
and `FPWholePlaneUpperVolumeTail`; the coordinate change `h2` and the cone mean-zero restriction `hR` stay named. -/
theorem hprev_of_shortWindow_frozen (h0 : MatedCRT.FPWholePlaneLQGExistence) (h2 : WholePlaneLQGCoordinateChangeStep)
    (hV : MatedCRT.FPWholePlaneUpperVolumeTail) (hR : ConeMeanZeroRestrictionStep) :
    ShortWindowGoodRadiusPrevalenceStmt :=
  shortWindowGoodRadiusPrevalence_closed h0 h2 hV hR

#print axioms MatedCRT.Lemma68Window.hprev_of_shortWindow_frozen

end MatedCRT.Lemma68Window
