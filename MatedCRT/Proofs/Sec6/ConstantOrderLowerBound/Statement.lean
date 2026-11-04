import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Walk
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Model

/-!
# Lemma 6.7 (lemma:constant-order-lower-bound, line 2410)

From Lemma 6.8 (the proof of lines 2449-2461) and the cited Section 2 inputs: Lemma 2.7 (volume growth, BG20
Lemma A.1), Lemma 2.8 (cell sizes, BG20 Lemma 2.4) and Lemma 2.19 (finite expected exit times), which supply the
facts left implicit in the printed proof (the walk exits, `V^ε(B_ρ)` is finite). The walk steps are proved.
-/

namespace MatedCRT

/-- **Lemma 6.7** from Lemma 6.8 and Lemmas 2.7, 2.8, 2.19, and `AdjacentCellsMeetAeStep` (adjacent vertices of the map
of Definition 1.1 have intersecting cells; a consequence of the mating-of-trees coupling, MatedCRT/Steps/Infra/
MatingOfTrees.lean, needed since the graph switch (L1)). -/
theorem constantOrderLowerBound (𝒮 : SpaceFillingSLEModel) (h68 : ConstantOrderLowerBoundDivStmt 𝒮)
    (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮)
    (hcell : AdjacentCellsMeetAeStep 𝒮) : ConstantOrderLowerBoundStmt 𝒮 :=
  constantOrderLowerBound_of_steps 𝒮 h68 srwHitDecompositionStep srwAeAdjacentStep
    (cellVerticesBallFiniteStep 𝒮 h27 h28) (walkExitsStep 𝒮 h27 h219) hcell

end MatedCRT
