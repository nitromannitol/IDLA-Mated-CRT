import MatedCRT.FirstPass.S5c

/-!
# FIRST PASS, Proposition 4.2 (prop:div-sandpile-lower-bound): assembly with the cone family (q4)

Task fp-S4d-4-2-assembly. `firstPass_4_2` (FirstPass/S5c.lean, q3) assembles `firstPass_4_1` (Theorem 4.1), the Section 2-3
inputs and `divSandpileLowerBound_final` (Proofs/Sec4/DivSandpileLowerBound/Final.lean). Its cone hypotheses enter only
through the measurability step `ConeFamilyAEMeasurableStep`, which is discharged by `coneFamilyAEMeasurable_proved`
(FirstPass/S2j.lean, q4, commit 7b51af3).

* `firstPass_4_2_of_coneFamilyStep`: the assembly with the single step `ConeFamilyAEMeasurableStep` as hypothesis.
* `firstPass_4_2_assembled`: the same conclusion, with the cone family step discharged by `coneFamilyAEMeasurable_proved`
  from its explicit hypotheses.

OPEN INPUT (not proved here): `hgap : HarmonicBallStrictObstacleGapStep 𝒮` (Proofs/Sec4/DivSandpileLowerBound/Final.lean:32),
the strict obstacle gap on the harmonic ball. Its printed proof, `eq:strictly-above-in-interior` of
paper/idla_mated_crt-corrected.tex (label at line 1913, "there exists s > 0 by continuity"), does not establish strict
positivity on the interior of the closure of the positivity set (audit E-x3-1, `StrictGapCounterexample.lean`); the missing
ingredient is (2) of audit E-c2-5. Both theorems below are therefore conditional on `hgap`.
-/

namespace MatedCRT

/-- **Proposition 4.2 (first pass), from the cone family step (q4).** Same hypotheses and conclusion as `firstPass_4_2`
(FirstPass/S5c.lean), except that the four cone hypotheses and the two cone external Props are replaced by the single step
`ConeFamilyAEMeasurableStep`. Conditional on the open strict gap `hgap`. -/
theorem firstPass_4_2_of_coneFamilyStep {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeEnvironmentScaling 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (hgap : HarmonicBallStrictObstacleGapStep 𝒮)
    (hfam : ConeFamilyAEMeasurableStep) :
    DivSandpileLowerBoundStmt 𝒮 :=
  divSandpileLowerBound_final 𝒮 (firstPass_4_1 hm h210 h34 h214 h28 h35 h218 h27 hH hcone) h23 h24 h27 h28 h33 hfam hgap

/-- **Proposition 4.2 (first pass), assembled (q4, fp-S4d-4-2-assembly).** The cone family step is discharged by
`coneFamilyAEMeasurable_proved` from the explicit cone hypotheses `hcan`, `hcl`, `hE1`, `hE2`, `hscale`, `h22`. The
conclusion is `DivSandpileLowerBoundStmt 𝒮`; the only open input is `hgap`. -/
theorem firstPass_4_2_assembled {𝒮 : SpaceFillingSLEModel}
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
  firstPass_4_2_of_coneFamilyStep hm h210 h34 h214 h28 h35 h218 h27 hH hcone h23 h24 h33 hgap
    (coneFamilyAEMeasurable_proved hcan hcl h27 hE1 hE2 hscale h22)

end MatedCRT
