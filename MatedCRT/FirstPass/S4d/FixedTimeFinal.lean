import MatedCRT.FirstPass.S4d.FixedTimeUnion
import MatedCRT.FirstPass.S4d.GlobalMeasurable
import MatedCRT.FirstPass.S4d.RescaledMeasurable
import MatedCRT.Proofs.Sec1.ConeScaleRadius

/-!
# The fixed-time union from the paper's dependencies (FIRST PASS, S4d, final interface)

`StrictGapFixedTimeUnionStep 𝒮` (ChatGPT §9, operator 01:25) from the Draft statements `h24` (Lemma 2.4), `h25`
(Lemma 2.5), the stopped measurability step `hfam` (supplied by `coneFamilyAEMeasurable_proved` in the assembly), `h26`
(Lemma 2.6, `ConeScaleInvarianceStmt`, explicit paper dependency) and the quantum-cone scaling input `hscale`, which gives
the positivity of the cone scale radii. The measurability of the global and rescaled pairs is proved (B2, B2R).
-/

open MeasureTheory Set Filter Topology Metric

namespace MatedCRT

/-- **StrictGapFixedTimeUnionStep from the dependencies** (ChatGPT §9 interface). -/
theorem strictGapFixedTimeUnionStep_of_steps (𝒮 : SpaceFillingSLEModel)
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt) (h25 : ConeScaleInvarianceUpToFixedTimeStmt)
    (hfam : ConeFamilyAEMeasurableStep) (h26 : ConeScaleInvarianceStmt) (hscale : QuantumConeScalingInput) :
    StrictGapFixedTimeUnionStep 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS Λ hΛ t ht
  have hP : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hF : IsConeField γ S.P S.hC S.hcirc S.μ :=
    ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩
  have hpos : ConeScaleRadiusPosStep := coneScaleRadiusPosStep_of_input hscale
  exact fixedTimeUnion_of_pair hΛ (coneGlobalFamilyAEMeasurable_of_stopped hγ hγ2 hF h24 h25 hfam hpos _ hΛ)
    (fun b hb => coneRescaledGlobalFamilyAEMeasurable_of_stopped hγ hγ2 hF h24 h25 hfam hpos _ hΛ hb)
    (fun b hb => h26 γ hγ hγ2 Ω S.P S.hC S.hcirc S.μ hF _ hΛ b hb)
    (fun b hb => hpos γ hγ hγ2 Ω S.P S.hC S.hcirc hP hS.isQuantumCone b hb) ht

end MatedCRT
