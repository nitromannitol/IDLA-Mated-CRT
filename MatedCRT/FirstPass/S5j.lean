import MatedCRT.FirstPass.S5d
import MatedCRT.FirstPass.S5i
import MatedCRT.FirstPass.S5g.MassLower
import MatedCRT.FirstPass.S3S4b

/-!
# Plumbing of Proposition 5.1 (fp-S5j, z8)

`firstPass_5_1_of_floorCell_pole` assembles the first-pass proof of Proposition 5.1 (the IDLA lower bound
`IDLALowerBoundStmt`, Draft Section 5) from the open-step composition `firstPass_5_1_of_open_steps`
(FirstPass/S5d.lean), discharging the inputs that have proved first-pass producers:

* `hfl` (the floor on the cells, `StoppedFloorCellStep`) is passed as the floor input `hfc`. The open-step theorem takes
  `StoppedFloorCellStep` itself and derives `StoppedFloorStep` and `StoppedFloorHalfStep` from it internally
  (`stoppedFloorStep_of_cellFloor`, `stoppedFloorHalfStep_of_cellFloor`, FirstPass/S5d/FloorCellStep.lean).
* `hmeas` (`ConeOriginNullMeasurableStep`, the ceiling input) is `coneOriginNullMeasurable_proved` (FirstPass/S5i.lean:38),
  from the frozen universal measurability of analytic sets `FrozenUniversalMeasurabilityOfAnalytic` (Frozen/S1c.lean:44).
* `hmass` (`StoppedMassLowerStep`, the second Green input) is `stoppedMassLower_proved` (FirstPass/S5g/MassLower.lean).
* `hconv` (`ConvergenceDivisibleStmt`, Draft Lemma 4.1) and `hgreen` (`UniformConvergenceGreenKernelStmt`, Draft Lemma 3.3)
  are `firstPass_4_1` and `firstPass_3_3` (FirstPass/S3S4.lean), fed by `firstPass_3_4` (FirstPass/S3S4b.lean; Draft Lemma 3.4)
  as `IntegralConvergenceGreenFunctionStmt`. The same route is used in `firstPass_1_4` (FirstPass/Main.lean).

The remaining hypotheses are the Draft statements, the frozen first-pass inputs (`FROZEN` in FirstPass/Frozen/*.lean) and the
open steps `StoppedPoleCellStep` (FirstPass/S5f/Steps.lean:39). No hypothesis is weakened.
-/

namespace MatedCRT

/-- **Proposition 5.1, plumbing (fp-S5j).** The IDLA lower bound `IDLALowerBoundStmt 𝒮` from the floor input
`StoppedFloorCellStep` (`hfc`), the pole input `StoppedPoleCellStep` (`hpole`, open) and the frozen universal measurability
`hU`, with the remaining Draft, frozen and external inputs as explicit hypotheses. -/
theorem firstPass_5_1_of_floorCell_pole (𝒮 : SpaceFillingSLEModel)
    -- Draft statements and cone inputs of `firstPass_5_1_of_open_steps`
    (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (hcan : ConeCanonicalHalfBallStep) (hcl : ConeHalfBallClosureInsideStep) (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep) (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt)
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt) (h218 : ExitTimeUpperBoundStmt 𝒮)
    -- the floor (cells), the pole (open) and the universal measurability (frozen)
    (hfc : StoppedFloorCellStep 𝒮) (hpole : StoppedPoleCellStep 𝒮) (hU : FrozenUniversalMeasurabilityOfAnalytic)
    -- inputs of `firstPass_3_4`, `firstPass_4_1` and `firstPass_3_3` (for `hconv` and `hgreen`)
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h211 : RandomWalkToLBMStmt 𝒮) (hrevuz : FrozenLBMGreenOccupation 𝒮) (hdet : FrozenTruncatedDetFixedTime 𝒮)
    (hexc : FrozenBrownianOutwardExcursionAtExit) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hEnv : FrozenConeEnvironmentScaling 𝒮)
    -- the remaining inputs of `stoppedMaxOutside_proved` and `stoppedSecondGreenStep_of_inputs`
    (hG : FrozenGreenDiscPole) (hG15 : GreenFunctionCrudeBoundStmt 𝒮) (hG16 : GreenKernelLowerBoundStmt 𝒮) :
    IDLALowerBoundStmt 𝒮 := by
  have h34 : IntegralConvergenceGreenFunctionStmt 𝒮 :=
    firstPass_3_4 h27 h218 hm h211 h28 hrevuz hdet hexc
  have hconv : ConvergenceDivisibleStmt 𝒮 := firstPass_4_1 hm h210 h34 h214 h28 h35 h218 h27 hH hEnv
  have hgreen : UniformConvergenceGreenKernelStmt 𝒮 := firstPass_3_3 h210 h34 h214 h28 h27 h218 hm hH
  exact firstPass_5_1_of_open_steps 𝒮 h27 h28 hcan hcl hE1 hE2 hscale h22 h24 hfc h218 hconv hgreen hm hG hpole
    (coneOriginNullMeasurable_proved 𝒮 hU) hG15 hG16 (stoppedMassLower_proved 𝒮)

end MatedCRT
