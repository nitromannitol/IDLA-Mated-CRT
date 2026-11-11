import MatedCRT.FirstPass.S4d.ScaleBridge
import MatedCRT.FirstPass.Frozen.S4d2

/-!
# FIRST PASS, rescaled half-ball horizon uniqueness `hRU`

`ConeRescaledHalfBallHorizonUniqueFPStep` (`FirstPass/S4d/ScaleBridge.lean`) is proved from the canonical half-ball
step `ConeCanonicalHalfBallStep`, the closure step `ConeHalfBallClosureInsideStep`, and the frozen cone-rescaling input
`ConeRescaledMeasureIsConeFieldInput` (`FirstPass/Frozen/S4d2.lean`). The argument: the rescaled measure of a cone field is
again a cone field (the frozen input), so `halfBallTime_eq_of_stopped_fp` identifies the stopping time of every family stopped
at `∂B_{1/2}` for that rescaled measure with its `halfBallTime`. A rescaled family of harmonic balls for `μ(ω)` is a family of
harmonic balls for `rescaledMeasure (μ ω) R b` (`coneHarmonicBallFamilyOnScalingStep`), so two rescaled stopped families both
have `halfBallTime` equal to their stopping times, which gives `S = T`.
-/

namespace MatedCRT

open MeasureTheory

/-- **Rescaled half-ball horizon uniqueness (`hRU`).** Proof of
`ConeRescaledHalfBallHorizonUniqueFPStep` from the canonical half-ball step, the closure step and the frozen input
`ConeRescaledMeasureIsConeFieldInput` (route A). -/
theorem coneRescaledHalfBallHorizonUnique_fp (hcan : ConeCanonicalHalfBallStep) (hcl : ConeHalfBallClosureInsideStep)
    (hrescale : ConeRescaledMeasureIsConeFieldInput) : ConeRescaledHalfBallHorizonUniqueFPStep := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone b hb
  obtain ⟨hR, hCb, hcircb, hconeb⟩ := hrescale γ hγ0 hγ2 Ω P hC hcirc μ hcone b hb
  have hId := halfBallTime_eq_of_stopped_fp hcan hcl γ hγ0 hγ2 Ω P hCb hcircb
    (fun ω => rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) hconeb
  filter_upwards [hR, hId] with ω hRω hIdω
  intro T S Λ Γ hT hΛ hΛstop hS hΓ hΓstop
  have hΛb := coneHarmonicBallFamilyOnScalingStep (μ ω) Λ (coneScaleRadius γ (hcirc ω) b) b T hRω hb hΛ
  have hΓb := coneHarmonicBallFamilyOnScalingStep (μ ω) Γ (coneScaleRadius γ (hcirc ω) b) b S hRω hb hΓ
  have hTId := hIdω T (rescaledFamily Λ (coneScaleRadius γ (hcirc ω) b) b) hT hΛb hΛstop
  have hSId := hIdω S (rescaledFamily Γ (coneScaleRadius γ (hcirc ω) b) b) hS hΓb hΓstop
  exact hSId.symm.trans hTId

end MatedCRT
