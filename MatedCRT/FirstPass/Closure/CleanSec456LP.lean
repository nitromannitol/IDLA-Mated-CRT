import MatedCRT.FirstPass.Closure.HLsRewire53
import MatedCRT.FirstPass.Closure.OwnBinderRewire
import MatedCRT.FirstPass.S6p
import MatedCRT.FirstPass.LPBridge.BrownianOutwardExcursion
import MatedCRT.FirstPass.LPBridge.ConeMeanZeroRestrictionFinal
import MatedCRT.FirstPass.SLERef.Certified

/-!
# Counted rows of Sections 4 and 6 with the LP-bridge binders discharged

Each `closed_<n>_lp` below has the conclusion of its own-binder wrapper and discharges only binders whose type is
the type of a committed concluder with no hypotheses of its own, or whose only hypotheses are binders of the wrapper:

* `closed_4_1_lp` (wrapper `firstPass_4_1_coneLaw_ownBinders`, `Closure/HLsRewire53.lean:65`): `hexc` is
  `frozenBrownianOutwardExcursionAtExit_holds` (`LPBridge/BrownianOutwardExcursion.lean:113`) and `hcone` is
  `CertifiedReferenceModel.frozenConeScaling hC` (`SLERef/Certified.lean:111`).
* `closed_4_8_lp` (wrapper `closed_4_8_corrected_ownBinders`, `Closure/OwnBinderRewire.lean:71`): `hexc` as above.
* `closed_6_4_lp` (wrapper `firstPass_6_4_uniform`, `S6p.lean:213`): `hR` is
  `ConeMeanZeroRestriction.fpConeMeanZeroRestriction_holds` (`LPBridge/ConeMeanZeroRestrictionFinal.lean:144`).
* `closed_6_10_lp` (wrapper `closed_6_10_ownBinders`, `Closure/OwnBinderRewire.lean:123`): `hR` as above.
-/

open MeasureTheory Set
open _root_.HarmonicBalls

namespace MatedCRT

/-- **Lemma 4.1 (cone law), LP-bridge form.** The conclusion is `ConvergenceDivisibleStmt 𝒮`, as for
`firstPass_4_1_coneLaw_ownBinders`; `hexc` and `hcone` are discharged, `hC` and `hBG` remain. -/
theorem closed_4_1_lp {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (hBG : FrozenBerestyckiGwynneConeBallMass) :
    ConvergenceDivisibleStmt 𝒮 :=
  firstPass_4_1_coneLaw_ownBinders ν hC hBG frozenBrownianOutwardExcursionAtExit_holds
    hC.frozenConeScaling

/-- **Lemma 4.8 (corrected subsequential properties), LP-bridge form.** The conclusion is
`SubsequentialPropertiesCorrectedStmt 𝒮`, as for `closed_4_8_corrected_ownBinders`; `hexc` is discharged. -/
theorem closed_4_8_lp (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (hBG : FrozenBerestyckiGwynneConeBallMass) :
    SubsequentialPropertiesCorrectedStmt 𝒮 :=
  closed_4_8_corrected_ownBinders 𝒮 ν hC hBG frozenBrownianOutwardExcursionAtExit_holds

/-- **Lemma 6.4 with `C = C(γ, c₀)`, LP-bridge form.** The conclusion is `GoodAnnulusPrevalenceUniformStmt`, as for
`FirstPass64.firstPass_6_4_uniform`; `hR` is discharged, `h0`, `h2`, `hV` remain. -/
theorem closed_6_4_lp (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail) : FirstPass64.GoodAnnulusPrevalenceUniformStmt :=
  FirstPass64.firstPass_6_4_uniform h0 h2 hV
    ConeMeanZeroRestriction.fpConeMeanZeroRestriction_holds

/-- **Lemma 6.10, LP-bridge form.** The conclusion is `IterativeBoundStmt 𝒮`, as for `closed_6_10_ownBinders`;
`hR` is discharged, `hC`, `hBG`, `h0`, `h2`, `hV` remain. -/
theorem closed_6_10_lp (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail) : IterativeBoundStmt 𝒮 :=
  closed_6_10_ownBinders 𝒮 ν hC hBG h0 h2 hV ConeMeanZeroRestriction.fpConeMeanZeroRestriction_holds

end MatedCRT

#print axioms MatedCRT.closed_4_1_lp
#print axioms MatedCRT.closed_4_8_lp
#print axioms MatedCRT.closed_6_4_lp
#print axioms MatedCRT.closed_6_10_lp
