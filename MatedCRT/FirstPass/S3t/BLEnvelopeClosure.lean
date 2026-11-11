import MatedCRT.FirstPass.S3t

/-!
# Brownian envelope closure for every valid environment

`blEnvelopeClosureInput_holds` proves the named input `BLEnvelopeClosureInput 𝒮` (`BoundaryShells.lean:221`) for every
fixed model `𝒮`. It is the measurable closure of a scalar LBM observable `lbm_scalar_measurable_of_bl_envelopes`
(`BLExtension.lean`; answer 46(a2) §1), applied with the bounded-Lipschitz measurability
`lbmPathFunctionalMeasurableStep_holds` (`PathFunctionalStep.lean`) and the almost sure continuity of the rescaled
LBM paths `ae_continuous_rescaledLBMPath` (`ContinuumUnderDiscrete.lean`).

`truncatedQuenchedLawsFixedTime_of_inputs` is the four-binder theorem: the closure variant
`truncatedQuenchedLawsFixedTime_of_inputs_closure` (`S3t.lean`) with this input supplied. It introduces no new
hypothesis and no new frozen Prop.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open _root_.HarmonicBalls

namespace MatedCRT.TruncatedLaws

/-- **The Brownian envelope closure holds for every fixed model.** For a valid environment `S` at `γ ∈ (0,2)` and
starting point `y`, a bounded path functional `H` that is continuous within the continuous paths at almost every
rescaled LBM path has almost surely strongly measurable Brownian values and an `AEMeasurable` Brownian integral in the
environment. The proof applies `lbm_scalar_measurable_of_bl_envelopes` with `𝒞 = {v | Continuous v}` (nonempty,
containing the zero path), the a.s. continuity `ae_continuous_rescaledLBMPath`, and the bounded-Lipschitz measurability
`lbmPathFunctionalMeasurableStep_holds`. -/
theorem blEnvelopeClosureInput_holds (𝒮 : SpaceFillingSLEModel) : BLEnvelopeClosureInput 𝒮 := by
  intro γ hγ0 hγ2 Ω _ S hS y H hbd hHcont
  obtain ⟨L, hL⟩ := hbd
  have hX𝒞 : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y,
      rescaledLBMPath (S.clock ω) S.m₀ b ∈ {v : ℝ≥0 → ℂ | Continuous v} :=
    ae_continuous_rescaledLBMPath Ω S hS y
  exact lbm_scalar_measurable_of_bl_envelopes {v : ℝ≥0 → ℂ | Continuous v} ⟨fun _ => 0, continuous_const⟩
    (fun ω b => rescaledLBMPath (S.clock ω) S.m₀ b) H hX𝒞 ⟨L, fun w _ => hL w⟩ hHcont
    (fun F hF => lbmPathFunctionalMeasurableStep_holds 𝒮 γ hγ0 hγ2 Ω S hS y F hF)

/-- **Truncated quenched laws at a fixed time, from the four binders.** The binders `h211 h28 hmeps hexit` are the
named inputs `RandomWalkToLBMStmt 𝒮`, `CellSizeEstimateStmt 𝒮`, `MepsScalingInput 𝒮` and
`BrownianOutwardExcursionAtExitStep`. The Brownian envelope closure `BLEnvelopeClosureInput 𝒮` is discharged by
`blEnvelopeClosureInput_holds`. -/
theorem truncatedQuenchedLawsFixedTime_of_inputs {𝒮 : SpaceFillingSLEModel}
    (h211 : RandomWalkToLBMStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮) (hmeps : MepsScalingInput 𝒮)
    (hexit : BrownianOutwardExcursionAtExitStep) :
    MatedCRT.FrozenTruncatedQuenchedLawsFixedTime 𝒮 :=
  truncatedQuenchedLawsFixedTime_of_inputs_closure h211 h28 hmeps hexit (blEnvelopeClosureInput_holds 𝒮)

end MatedCRT.TruncatedLaws
