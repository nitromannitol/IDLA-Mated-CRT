import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.CrudeShell
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells

/-! The crude confinement estimates with adjacent-cell contact discharged. -/

namespace MatedCRT.Sec7

/-- Crude confinement on the ambient closure, from the numbered inputs. -/
theorem crude_confinement_polyHighProb_of_inputs
    (𝒮 : SpaceFillingSLEModel) (hcell : CellSizeEstimateStmt 𝒮)
    (hcrude : CrudeUpperBoundStmt 𝒮) :
    type_of% (crude_confinement_polyHighProb 𝒮 hcell hcrude (adjacentCellsMeetAeStep 𝒮)) :=
  crude_confinement_polyHighProb 𝒮 hcell hcrude (adjacentCellsMeetAeStep 𝒮)

/-- Fixed-radius crude confinement, from the numbered inputs. -/
theorem crude_confinement_fixed_radius_polyHighProb_of_inputs
    (𝒮 : SpaceFillingSLEModel) (hcell : CellSizeEstimateStmt 𝒮)
    (hcrude : CrudeUpperBoundStmt 𝒮) :
    type_of% (crude_confinement_fixed_radius_polyHighProb 𝒮 hcell hcrude
      (adjacentCellsMeetAeStep 𝒮)) :=
  crude_confinement_fixed_radius_polyHighProb 𝒮 hcell hcrude (adjacentCellsMeetAeStep 𝒮)

/-- Crude confinement without an ambient closure assumption. -/
theorem crude_confinement_without_closure_hypothesis_of_inputs
    (𝒮 : SpaceFillingSLEModel) (hcell : CellSizeEstimateStmt 𝒮)
    (hcrude : CrudeUpperBoundStmt 𝒮) :
    type_of% (crude_confinement_without_closure_hypothesis 𝒮 hcell hcrude
      (adjacentCellsMeetAeStep 𝒮)) :=
  crude_confinement_without_closure_hypothesis 𝒮 hcell hcrude (adjacentCellsMeetAeStep 𝒮)

/-- An intermediate shell confines the stopped cluster, from the numbered inputs. -/
theorem stopped_filled_confinement_of_intermediate_shell_of_inputs
    (𝒮 : SpaceFillingSLEModel) (hcell : CellSizeEstimateStmt 𝒮)
    (hcrude : CrudeUpperBoundStmt 𝒮) :
    type_of% (stopped_filled_confinement_of_intermediate_shell 𝒮 hcell hcrude
      (adjacentCellsMeetAeStep 𝒮)) :=
  stopped_filled_confinement_of_intermediate_shell 𝒮 hcell hcrude (adjacentCellsMeetAeStep 𝒮)

end MatedCRT.Sec7
