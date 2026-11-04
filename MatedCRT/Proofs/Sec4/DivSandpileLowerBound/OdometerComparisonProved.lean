import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.OdometerComparison
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells

/-! # Divisible-sandpile odometer comparison -/

namespace MatedCRT

/-- The odometer comparison holds for the mated-CRT map. -/
theorem divSandpileOdometerComparison (𝒮 : SpaceFillingSLEModel) :
    DivSandpileOdometerComparisonStep 𝒮 :=
  divSandpileOdometerComparison_of_cellsMeet (adjacentCellsMeetAeStep 𝒮)

/-- Proposition 4.2 follows from the obstacle-cluster inner approximation and
the stated convergence and geometric estimates. -/
theorem divSandpileLowerBound_of_inputs (𝒮 : SpaceFillingSLEModel)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h23 : ConeHarmonicBallsStmt)
    (h213 : MaximumPrincipleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (happrox : ObstacleClusterInnerApproximationStep 𝒮) :
    DivSandpileLowerBoundStmt 𝒮 :=
  divSandpileLowerBound_of_steps 𝒮 h41 h23 h213 h33 h28 happrox
    (divSandpileOdometerComparison 𝒮)

end MatedCRT
