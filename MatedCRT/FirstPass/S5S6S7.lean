import MatedCRT.Draft.Section5
import MatedCRT.Proofs.Measurability.EnvSigma
import MatedCRT.Proofs.Sec5.LLowerBound.OfInputs

/-!
# FIRST PASS: Section 5 (Proposition 5.1 and Lemmas 5.2-5.4) of arXiv:2211.04891 (corrected draft)

Each theorem `firstPass_<sec>_<num>` has as conclusion the Draft statement of the numbered result and, as
hypotheses, only Draft statements of other numbered results used by the printed proof and EXTERNAL inputs.
-/

namespace MatedCRT

/-- **Lemma 5.2** (`firstPass_5_2`). Uses the cited Lemmas 2.7 (`VolumeGrowthStmt`) and 2.8
(`CellSizeEstimateStmt`). -/
theorem firstPass_5_2 (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮) :
    GeneralIDLALowerBoundStmt 𝒮 :=
  generalIDLALowerBound_of_volumeGrowth_cellSize 𝒮 h27 h28

/-- **Lemma 5.4** (`firstPass_5_4`). Uses the cited Lemmas 2.15, 2.16 and 2.9; the adjacency of cells is
proved (`adjacentCellsMeetAeStep`). -/
theorem firstPass_5_4 (𝒮 : SpaceFillingSLEModel) (h215 : GreenFunctionCrudeBoundStmt 𝒮)
    (h216 : GreenKernelLowerBoundStmt 𝒮) (h29 : CountingMeasureConvergenceStmt 𝒮) : LLowerBoundStmt 𝒮 :=
  lLowerBound_of_inputs 𝒮 h215 h216 h29

end MatedCRT
