import MatedCRT.External.QuantumCone
import MatedCRT.Proposed.BerestyckiGwynne
import MatedCRT.FirstPass.Frozen.S5Cited
import MatedCRT.Proofs.Sec1.ConeScaleRadius
import MatedCRT.Proofs.Sec3.ConeBallMass
import MatedCRT.Proofs.Sec2.LQGMeasureProperties.NonAtomicScaling
import MatedCRT.FirstPass.S2y.LateralAssembly250
import MatedCRT.FirstPass.S2y.ConeCircleAbsApprox
import MatedCRT.Steps.Sec2.LQGMeasureProperties

/-!
# Fact 2.2 (LQG area measure of the quantum cone) from its literature inputs

`closed_2_2_lit` proves `LQGMeasurePropertiesStmt` (Fact 2.2, `fact:lqg-measure`, paper line 474) from the binders
below. The proof goes through `LQGMeasure.lqgMeasureProperties_of_volumeGrowth`:

* the volume growth Lemma 2.7 (`VolumeGrowthStmt`) from the Berestycki-Gwynne ball-mass estimate
  (`volumeGrowthStmt_of_berestyckiGwynne`, input `FrozenBerestyckiGwynneConeBallMass`);
* the locality of the circle averages (`ConeCircleAverageLocalityStep`, `coneCircleAverageLocalityStep_proved`, no binder);
* the scale invariance of the quantum cone (`ConeFieldScalingStep`, `coneFieldScalingStep_proved_radial`) and the
  positivity of the cone scale radius (`ConeScaleRadiusPosStep`, `coneScaleRadiusPosStep_of_input`), both from the
  quantum cone scaling input `QuantumConeScalingInput` (DMS14 Proposition 4.13(i));
* the conformal covariance of the LQG measure for the non-dyadic dilations `φ(z) = s z`, `1 < s < 2`, which is
  `LQGMeasureNonDyadicDilationPart` (DS11 Proposition 2.1 for a fixed map; SW16 for all maps simultaneously).

Non-atomicity, locality, Weyl scaling and the dilations by powers of `2` are proved from the definition of the LQG
measure as a vague limit along the dyadic scales.
-/

namespace MatedCRT

/-- **Fact 2.2, from the literature inputs.** The binders are: `hscale`, the quantum cone scaling input
`QuantumConeScalingInput` (`MatedCRT/External/QuantumCone.lean`); `hBG`, the Berestycki-Gwynne ball-mass estimate
`FrozenBerestyckiGwynneConeBallMass` (`MatedCRT/FirstPass/Frozen/S5Cited.lean`); `hND`, the conformal covariance of the
LQG measure for the non-dyadic dilations, `LQGMeasureNonDyadicDilationPart`
(`MatedCRT/Steps/Sec2/LQGMeasureProperties.lean`). -/
theorem closed_2_2_lit
    (hscale : QuantumConeScalingInput)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hND : LQGMeasureNonDyadicDilationPart) :
    LQGMeasurePropertiesStmt :=
  LQGMeasure.lqgMeasureProperties_of_volumeGrowth (volumeGrowthStmt_of_berestyckiGwynne hBG) hND
    coneCircleAverageLocalityStep_proved (LQGMeasure.coneFieldScalingStep_proved_radial hscale)
    (coneScaleRadiusPosStep_of_input hscale)

end MatedCRT
