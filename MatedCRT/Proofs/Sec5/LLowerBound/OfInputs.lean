import MatedCRT.Proofs.Sec5.LLowerBound.OfEvents
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells

/-! Lemma 5.4 from its cited inputs, using the adjacency of cells. -/

namespace MatedCRT

/-- The Green-sum step follows from the proved adjacency of mated-CRT cells. -/
theorem lLowerBoundSumStep_of_inputs (𝒮 : SpaceFillingSLEModel) :
    LLowerBoundSumStep 𝒮 :=
  lLowerBoundSumStep_of_adjacentCellsMeet 𝒮 (adjacentCellsMeetAeStep 𝒮)

/-- Lemma 5.4 follows from the three estimates cited in its proof. -/
theorem lLowerBound_of_inputs (𝒮 : SpaceFillingSLEModel)
    (h215 : GreenFunctionCrudeBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) : LLowerBoundStmt 𝒮 :=
  lLowerBound_of_adjacentCellsMeet 𝒮 h215 h216 h29 (adjacentCellsMeetAeStep 𝒮)

end MatedCRT
