import MatedCRT.FirstPass.S4e.RescaledDecode
import MatedCRT.FirstPass.S4d.ConeScaleConstancy
import MatedCRT.Proofs.Sec1.ConeScaleRadius

/-!
# hB2R from the global-pair step: the rescaled pair is a.e. measurable

This is hB2R of `firstPass_4_2_of_scale_inputs` (S4d.lean:183-184). The exact type `ConeRescaledPairAEMeasurableStep` is S4d/ConeScaleConstancy.lean:38.

The theorem below proves hB2R from the named global-pair step `hB2` and the scale-radius positivity `hpos`
(`ConeScaleRadiusPosStep`, Steps/Sec2/ConeScaleInvarianceUpToFixedTime.lean:51), which the rescaled circle part needs.
-/

open MeasureTheory

namespace MatedCRT.FirstPass.S4e

/-- **hB2R from hB2.** Given the global-pair step `hB2` and the scale-radius positivity `hpos`, for every cone field and
every a.s. cone harmonic ball family `Λ`, and every `b > 0`, the rescaled pair `(rescaled circle process, rescaled global
family process)` of Lemma 2.6 is a.e. measurable. The circle part is `coneRescaledCircleAEMeasurableStep_of_pos`; the
family part is `aemeasurable_rescaledGlobalFamilyProcess`, fed with the second component of `hB2`. -/
theorem coneRescaledPairAEMeasurableStep_of_globalPair (hB2 : ConeGlobalFamilyPairAEMeasurableStep)
    (hpos : ConeScaleRadiusPosStep) : ConeRescaledPairAEMeasurableStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hF Λ hΛ b hb
  have hG : AEMeasurable (fun ω => (circleProcess (hcirc ω), globalFamilyProcess (Λ ω))) P :=
    hB2 γ hγ hγ2 Ω P hC hcirc μ hF Λ hΛ
  have hcirc' : AEMeasurable (fun ω => circleProcess (rescaledCircle γ (hcirc ω)
      (coneScaleRadius γ (hcirc ω) b) b)) P :=
    coneRescaledCircleAEMeasurableStep_of_pos hpos γ hγ hγ2 Ω P hC hcirc μ hF b hb
  exact hcirc'.prodMk (aemeasurable_rescaledGlobalFamilyProcess hF.2.1 Λ hΛ hG.snd hb)

/-- **hB2R from hB2 and the quantum cone scaling input.** The positivity `hpos` of
`coneRescaledPairAEMeasurableStep_of_globalPair` is derived from the literature input `QuantumConeScalingInput`
(DMS14 Proposition 4.13(i), MatedCRT/External/QuantumCone.lean:19) by `coneScaleRadiusPosStep_of_input`, so the only
remaining named hypothesis is `hB2`. -/
theorem coneRescaledPairAEMeasurableStep_of_scalingInput (hB2 : ConeGlobalFamilyPairAEMeasurableStep)
    (hscale : QuantumConeScalingInput) : ConeRescaledPairAEMeasurableStep :=
  coneRescaledPairAEMeasurableStep_of_globalPair hB2 (coneScaleRadiusPosStep_of_input hscale)

end MatedCRT.FirstPass.S4e
