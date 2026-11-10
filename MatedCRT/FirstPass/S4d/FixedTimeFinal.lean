import MatedCRT.FirstPass.S4d.FixedTimeUnion
import MatedCRT.FirstPass.S4d.GlobalMeasurable
import MatedCRT.FirstPass.S4d.RescaledMeasurable
import MatedCRT.FirstPass.S4d.Provider24
import MatedCRT.Proofs.Sec1.ConeScaleRadius

/-!
# The fixed-time union from the paper's dependencies (FIRST PASS, S4d, final interface)

`StrictGapFixedTimeUnionStep 𝒮` (ChatGPT §9, operator 01:25) from the Draft statements `h24` (Lemma 2.4), `h25`
(Lemma 2.5), the stopped measurability step `hfam` (supplied by `coneFamilyAEMeasurable_proved` in the assembly), `h26`
(Lemma 2.6, `ConeScaleInvarianceStmt`, explicit paper dependency) and the quantum-cone scaling input `hscale`, which gives
the positivity of the cone scale radii. The measurability of the global and rescaled pairs is proved (B2, B2R).

The core `strictGapFixedTimeUnionStep_of_exists` uses only the existence clause `ConeStoppedBaseExistsFP4` of Lemma 2.4.
The Draft entry point `strictGapFixedTimeUnionStep_of_steps` and the provider entry point
`strictGapFixedTimeUnionStep_of_provider` (`ConeHarmonicBallsProviderFP4`, FirstPass/S4d/Provider24.lean) are both
corollaries of the core.
-/

open MeasureTheory Set Filter Topology Metric

namespace MatedCRT

/-- **StrictGapFixedTimeUnionStep from the existence clause of Lemma 2.4** (q4, fp-S4d-4-2-h24-gate-consumers). The
uniqueness clause `T' = T` of the Draft `ConeHarmonicBallsUpToFixedTimeStmt` is not used. -/
theorem strictGapFixedTimeUnionStep_of_exists (𝒮 : SpaceFillingSLEModel)
    (hexist : ConeStoppedBaseExistsFP4) (h25 : ConeScaleInvarianceUpToFixedTimeStmt)
    (hfam : ConeFamilyAEMeasurableStep) (h26 : ConeScaleInvarianceStmt) (hscale : QuantumConeScalingInput) :
    StrictGapFixedTimeUnionStep 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS Λ hΛ t ht
  have hP : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hF : IsConeField γ S.P S.hC S.hcirc S.μ :=
    ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩
  have hpos : ConeScaleRadiusPosStep := coneScaleRadiusPosStep_of_input hscale
  exact fixedTimeUnion_of_pair hΛ (coneGlobalFamilyAEMeasurable_of_exists hγ hγ2 hF hexist h25 hfam hpos _ hΛ)
    (fun b hb => coneRescaledGlobalFamilyAEMeasurable_of_exists hγ hγ2 hF hexist h25 hfam hpos _ hΛ hb)
    (fun b hb => h26 γ hγ hγ2 Ω S.P S.hC S.hcirc S.μ hF _ hΛ b hb)
    (fun b hb => hpos γ hγ hγ2 Ω S.P S.hC S.hcirc hP hS.isQuantumCone b hb) ht

/-- **StrictGapFixedTimeUnionStep from the Draft Lemma 2.4** (`ConeHarmonicBallsUpToFixedTimeStmt`; signature unchanged
for S4d.lean:218). Used only through `coneStoppedBaseExists_of_draft`. -/
theorem strictGapFixedTimeUnionStep_of_steps (𝒮 : SpaceFillingSLEModel)
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt) (h25 : ConeScaleInvarianceUpToFixedTimeStmt)
    (hfam : ConeFamilyAEMeasurableStep) (h26 : ConeScaleInvarianceStmt) (hscale : QuantumConeScalingInput) :
    StrictGapFixedTimeUnionStep 𝒮 :=
  strictGapFixedTimeUnionStep_of_exists 𝒮 (coneStoppedBaseExists_of_draft h24) h25 hfam h26 hscale

/-- **StrictGapFixedTimeUnionStep from the provider form of Lemma 2.4** (`ConeHarmonicBallsProviderFP4`,
FirstPass/S4d/Provider24.lean; chat 174 decision: the chain takes the provider form, not the Draft with `T' = T`). -/
theorem strictGapFixedTimeUnionStep_of_provider (𝒮 : SpaceFillingSLEModel)
    (hprov : ConeHarmonicBallsProviderFP4) (h25 : ConeScaleInvarianceUpToFixedTimeStmt)
    (hfam : ConeFamilyAEMeasurableStep) (h26 : ConeScaleInvarianceStmt) (hscale : QuantumConeScalingInput) :
    StrictGapFixedTimeUnionStep 𝒮 :=
  strictGapFixedTimeUnionStep_of_exists 𝒮 (coneStoppedBaseExists_of_provider hprov) h25 hfam h26 hscale

end MatedCRT
