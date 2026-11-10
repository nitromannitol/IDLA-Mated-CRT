import MatedCRT.FirstPass.S3S4c
import MatedCRT.FirstPass.Frozen.S3S4
import MatedCRT.FirstPass.S3t

/-!
# Lemma 3.4 with the truncated quenched laws derived (fp-S3t-consumers, z5)

`firstPass_3_4_derived` is `MatedCRT.S3S4c.firstPass_3_4` (`FirstPass/S3S4c.lean:149`) with the frozen hypothesis
`hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮` removed. The input is the local hypothesis `hT`, which stands for the
derivation `truncatedQuenchedLawsFixedTime_of_inputs` (z8, `FirstPass/S3t.lean`, not yet committed) with arguments
`h211`, `h28`, `hm`, `hexc` (note `notes/fp-gaps/CHATGPT-idla-3-4-truncated-laws.md` §4). When z8 commits that theorem,
replace `hT` by it. The old `firstPass_3_4` is unchanged. Terminology: Berestycki–Powell, Armitage–Gardiner for the
Green function; Duplantier–Sheffield for the LQG measure.
-/

namespace MatedCRT

/-- **Lemma 3.4 (integral convergence of the Green function), truncated quenched laws derived.** Same conclusion as
`MatedCRT.S3S4c.firstPass_3_4`; the frozen input `hdet` is replaced by `hT` applied to `h211`, `h28`, `hm`, `hexc`. -/
theorem firstPass_3_4_derived {𝒮 : SpaceFillingSLEModel} (h27 : VolumeGrowthStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hm : MepsScalingInput 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h211 : RandomWalkToLBMStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hT : RandomWalkToLBMStmt 𝒮 → CellSizeEstimateStmt 𝒮 → MepsScalingInput 𝒮 →
      BrownianOutwardExcursionAtExitStep → FrozenTruncatedQuenchedLawsFixedTime 𝒮) :
    IntegralConvergenceGreenFunctionStmt 𝒮 :=
  S3S4c.firstPass_3_4 h27 h218 hm hrevuz (hT h211 h28 hm hexc)

#print axioms firstPass_3_4_derived

open _root_.HarmonicBalls MeasureTheory Set Filter Topology MatedCRT.TruncatedLaws in
/-- **Lemma 3.4 (integral convergence of the Green function), truncated quenched laws derived from the staged theorem.**
Same conclusion as `MatedCRT.S3S4c.firstPass_3_4`. The frozen input `hdet` is replaced by
`MatedCRT.TruncatedLaws.truncatedQuenchedLawsFixedTime_of_inputs_staged` (`FirstPass/S3t.lean:329`) applied to `h211`, `h28`,
`hm`, `hexc`. The two routed Brownian measurability facts `hmeas` and `hShellMeas` (exact types of the staged theorem) are
named binders; drop them once z10 commits them or z8 commits `truncatedQuenchedLawsFixedTime_of_inputs`. -/
theorem firstPass_3_4_derived_staged {𝒮 : SpaceFillingSLEModel} (h27 : VolumeGrowthStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hm : MepsScalingInput 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h211 : RandomWalkToLBMStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hmeas : ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ (y z : ℂ) (s T : ℝ), 0 ≤ T → ∀ᵐ ω ∂S.P, AEStronglyMeasurable
        (fun b => stoppedOccupation (Metric.ball z s) T (fun _ => 1) (rescaledLBMPath (S.clock ω) S.m₀ b))
        (planarBrownianMotion y))
    (hShellMeas : ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ (y z : ℂ) (r T : ℝ) (n : ℕ), y ∈ Metric.ball z r → 0 ≤ T → AEMeasurable
        (fun ω => ∫ b, shellTime (ballExhaustion z r ((r - dist y z) / 2) n) (Metric.ball z r) T
          (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion y) S.P) :
    IntegralConvergenceGreenFunctionStmt 𝒮 :=
  S3S4c.firstPass_3_4 h27 h218 hm hrevuz
    (truncatedQuenchedLawsFixedTime_of_inputs_staged h211 h28 hm hexc hmeas hShellMeas)

#print axioms firstPass_3_4_derived_staged

end MatedCRT
