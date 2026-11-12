import MatedCRT.FirstPass.Derived.ConeDilationRatioHolds
import MatedCRT.FirstPass.S2y.LateralAssembly250
import MatedCRT.Proofs.Sec1.ConeScaleRadius
import MatedCRT.Proofs.Sec2.LQGMeasureProperties.Main
import MatedCRT.Proofs.Sec2.LQGMeasureProperties.NonAtomicScaling
import MatedCRT.FirstPass.Frozen.S4d2

/-!
# The rescaled cone measure is the LQG measure of a cone field

`ConeRescaledMeasureIsConeFieldInput` (FirstPass/Frozen/S4d2.lean) asks, for a γ-quantum cone field `(hC, hcirc)` with
LQG measure `μ` and `b > 0`, that almost surely the cone scale radius `R_b` is positive and that the rescaled measure
`rescaledMeasure μ R_b b` is the LQG measure of a cone field on the same probability space.

It follows from the scale invariance of the quantum cone through its circle average process
(`QuantumConeScalingInput`, DMS14 Proposition 4.13(i)) and the non-dyadic dilation part of Fact 2.2:
* the circle-average form of the scale invariance gives a version `(hC', hcirc')` of the field
  `h(R_b ·) + Q log R_b - γ⁻¹ log b` which is a quantum cone (`coneFieldScalingStep_proved_radial`, through the pairing
  decoder), and `R_b > 0` almost surely (`coneScaleRadiusPosStep_of_input`);
* the dilation covariance of the LQG measure (from `lqgMeasureNonDyadicDilationPart_holds`) and constant Weyl scaling
  identify the LQG measure of that field with `rescaledMeasure μ R_b b` (`coneLQGScalingStep_of_dilation`).

## Main results
* `coneRescaledMeasureIsConeFieldInput_of_scaling`: `QuantumConeScalingInput → ConeRescaledMeasureIsConeFieldInput`.
-/

open MeasureTheory HarmonicBalls

namespace MatedCRT.FirstPass.Derived

/-- **The rescaled cone measure is the LQG measure of a cone field**, from the scale invariance of the quantum cone
through its circle average process (DMS14 Proposition 4.13(i)). -/
theorem coneRescaledMeasureIsConeFieldInput_of_scaling (hscale : QuantumConeScalingInput) :
    ConeRescaledMeasureIsConeFieldInput := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone b hb
  have hL := MatedCRT.LQGMeasure.coneLQGScalingStep_of_dilation
    (MatedCRT.LQGMeasure.lqgMeasureDilationCovariancePart_of_nonDyadic lqgMeasureNonDyadicDilationPart_holds)
    (coneScaleRadiusPosStep_of_input hscale) γ hγ0 hγ2 Ω P hC hcirc μ hcone b hb
  obtain ⟨hC', hcirc', hQ', hae⟩ := MatedCRT.LQGMeasure.coneFieldScalingStep_proved_radial hscale γ hγ0 hγ2 Ω P
    hC hcirc hcone.1 hcone.2.1 b hb
  refine ⟨hL.mono fun ω h => h.1, hC', hcirc', ⟨hcone.1, hQ', ?_⟩⟩
  show ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc' ω) (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b)
  filter_upwards [hL, hae] with ω h1 h2
  rw [h2]
  exact h1.2

end MatedCRT.FirstPass.Derived
