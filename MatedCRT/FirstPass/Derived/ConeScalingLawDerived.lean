import MatedCRT.FirstPass.Derived.QuantumConeScalingDerived
import MatedCRT.FirstPass.Derived.ConeRescaledFieldHolds
import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.MeasureLaw
import MatedCRT.FirstPass.Frozen.S4S6c

/-!
# Cone scaling in law, from the scale invariance of the quantum cone

`FrozenConeScalingLaw 𝒮` (FirstPass/Frozen/S4S6c.lean) asks, for every valid environment `S` with cone parameter `γ`
and every `b > 0`, that the cone scale radius `R_b` is almost surely positive and almost everywhere measurable, that the
LQG measure `S.μ` and the rescaled measure `b⁻¹ μ_h(R_b ·)` are almost everywhere measurable random measures, and that
the rescaled measure has the law of `S.μ` (Duplantier-Miller-Sheffield, arXiv:1409.7055v4, Proposition 4.13(i), with the
dilation covariance of the LQG measure).

It follows, for every space-filling SLE model `𝒮`, from the circle-average form of the scale invariance of the quantum
cone (`QuantumConeScalingInput`, proved as `quantumConeScalingInput_derived`) and the dilation covariance of the LQG
measure (`lqgMeasureNonDyadicDilationPart_holds`): the quantum cone, the LQG measure and the probability measure of a
valid environment form a cone field (`IsConeField`), and the law of the rescaled measure is
`IsConeField.identDistrib_rescaledMeasure`.

## Main results
* `coneLQGScalingStep_of_scaling`: `QuantumConeScalingInput → ConeLQGScalingStep`.
* `frozenConeScalingLaw_of_scaling`: `QuantumConeScalingInput → FrozenConeScalingLaw 𝒮`.
* `frozenConeScalingLaw_derived`: `FrozenConeScalingLaw 𝒮` for every `𝒮`, with no hypothesis.
-/

open MeasureTheory ProbabilityTheory

namespace MatedCRT.FirstPass.Derived

/-- The coordinate change for the rescaled cone measure (`ConeLQGScalingStep`): the cone scale radius is positive and
`b⁻¹ μ_h(R_b ·)` is the LQG measure of the rescaled circle averages, from the scale invariance of the quantum cone
(through the positivity of `R_b`) and the dilation covariance of the LQG measure. -/
theorem coneLQGScalingStep_of_scaling (hscale : QuantumConeScalingInput) : ConeLQGScalingStep :=
  MatedCRT.LQGMeasure.coneLQGScalingStep_of_dilation
    (MatedCRT.LQGMeasure.lqgMeasureDilationCovariancePart_of_nonDyadic lqgMeasureNonDyadicDilationPart_holds)
    (coneScaleRadiusPosStep_of_input hscale)

/-- **Cone scaling in law**, from the scale invariance of the quantum cone (DMS14 Proposition 4.13(i)). -/
theorem frozenConeScalingLaw_of_scaling (hscale : QuantumConeScalingInput) (𝒮 : SpaceFillingSLEModel) :
    FrozenConeScalingLaw 𝒮 := by
  intro γ hγ0 hγ2 Ω _ S hS b hb
  have hcone : IsConeField γ S.P S.hC S.hcirc S.μ :=
    ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩
  have hlqg := coneLQGScalingStep_of_scaling hscale
  have hs := hlqg γ hγ0 hγ2 Ω S.P S.hC S.hcirc S.μ hcone b hb
  have hR : ∀ᵐ ω ∂S.P, 0 < coneScaleRadius γ (S.hcirc ω) b := hs.mono fun _ h => h.1
  exact ⟨hR, Sec1.aemeasurable_coneScaleRadius hcone.2.1 hR, hcone.aemeasurable_lqgMeasure,
    hcone.aemeasurable_rescaledMeasure b hR,
    (hcone.identDistrib_rescaledMeasure hγ0 hγ2 hscale hlqg hb).map_eq⟩

/-- **`FrozenConeScalingLaw` holds** for every space-filling SLE model `𝒮`. -/
theorem frozenConeScalingLaw_derived (𝒮 : SpaceFillingSLEModel) : FrozenConeScalingLaw 𝒮 :=
  frozenConeScalingLaw_of_scaling quantumConeScalingInput_derived 𝒮

end MatedCRT.FirstPass.Derived
