import MatedCRT.FirstPass.S3S4
import MatedCRT.FirstPass.S2j
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.Final

/-!
# FIRST PASS, Proposition 4.2 (prop:div-sandpile-lower-bound): assembly (q3)

`firstPass_4_2` is the first-pass form of Proposition 4.2 (`DivSandpileLowerBoundStmt`, Draft/Section4.lean:50). It
composes the proved first-pass Section 4 steps (`firstPass_4_1`, Theorem 4.1, in FirstPass/S3S4.lean; the
measurability of the cone family, `coneFamilyAEMeasurable_proved`, FirstPass/S2j.lean) with the proof
`divSandpileLowerBound_final` (Proofs/Sec4/DivSandpileLowerBound/Final.lean). No step of Proposition 4.2 itself is
assumed; the hypotheses are the cited inputs and the open first-pass steps listed in the report.
-/

namespace MatedCRT

/-- **Proposition 4.2** (first pass): the divisible sandpile lower bound `B⁻_δ(Λ_t) ⊆ D̄_ε(t ε⁻¹)`, from the
hypotheses of Theorem 4.1 (`firstPass_4_1`), the cited Section 2-3 inputs and the cone measurability chain. -/
theorem firstPass_4_2 {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeEnvironmentScaling 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (hgap : HarmonicBallStrictObstacleGapStep 𝒮)
    (hcan : ConeCanonicalHalfBallStep) (hcl : ConeHalfBallClosureInsideStep)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt) :
    DivSandpileLowerBoundStmt 𝒮 :=
  divSandpileLowerBound_final 𝒮 (firstPass_4_1 hm h210 h34 h214 h28 h35 h218 h27 hH hcone) h23 h24 h27 h28 h33
    (coneFamilyAEMeasurable_proved hcan hcl h27 hE1 hE2 hscale h22) hgap

end MatedCRT
