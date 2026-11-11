import MatedCRT.Proofs.Sec4.ObstacleSpecialization.Statements
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells

/-!
# FIRST PASS, Lemma 5.3: conservation of mass input (G-5-3 note, Section 2, eq. (7))

The mass bound `|Λ^ε_t| ≤ t ε⁻¹` of the discrete cluster (Draft Lemma 4.5, `DiscreteConservationOfMassCorrectedStmt`)
is PROVED from the proved cell-adjacency fact `AdjacentCellsMeetAeStep` (Proofs/MatingOfTrees/AdjacentCells.lean:17)
via `discreteConservationOfMassCorrected_of_escape` (Proofs/Sec4/ObstacleSpecialization/Statements.lean). So the mass
bound needs no antecedent of `MeanValueSurplusLowerStep`. The Lean chain goes through the obstacle specialization of
Appendix A to the connected component of the origin (Escape.lean:435 `matedConservationOfMass_of_regular`).
-/

namespace MatedCRT.S5c

/-- The conservation-of-mass input of Lemma 5.3 (G-5-3 Section 2, eq. (7)): `DiscreteConservationOfMassCorrectedStmt`
holds unconditionally, since `AdjacentCellsMeetAeStep` is proved. -/
theorem discreteConservationOfMass_proved (𝒮 : SpaceFillingSLEModel) : DiscreteConservationOfMassCorrectedStmt 𝒮 :=
  MatedCRT.discreteConservationOfMassCorrected_of_escape (MatedCRT.adjacentCellsMeetAeStep 𝒮)

end MatedCRT.S5c
