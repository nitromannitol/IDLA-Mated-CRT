import MatedCRT.Proofs.Sec6.IterativeBound.OfSteps
import MatedCRT.Proofs.Sec6.IterativeBound.Walk
import MatedCRT.Proofs.Sec6.IterativeBound.Quenched
import MatedCRT.Proofs.Sec6.IterativeBound.FieldSigma
import MatedCRT.Proofs.Sec6.AbelianIDLA.Statement

/-!
# Lemma 6.10 (lemma:iterative-bound, line 2694)

`iterativeBound`: Lemma 6.10 from Lemma 6.9 (in the E-A10 (b) form, `ChanceOfBeingAbsorbedLogLossStmt`), Lemma 2.8 and
the intersection of the cells of adjacent vertices (`AdjacentCellsMeetStep`, Definitions 1.1 = 1.2, INPUT-REQUESTS
IR-A2). The other steps are proved: Lemma 6.3 for arbitrary starting sites (`AbelianIDLA.abelianIDLAAnyStartStep`),
the walk path property (`srwPathStep`), the measurability of the field (`fieldSigmaMeasurableStep`, from
`IsQuantumCone.measurable_pairing`) and the quenched iteration (`IterativeBound.quenchedIterationStep`).
-/

namespace MatedCRT

/-- **Lemma 6.10** from Lemma 6.9 (E-A10 (b) form), Lemma 2.8 and the adjacency of cells. -/
theorem iterativeBound (𝒮 : SpaceFillingSLEModel) (h69 : ChanceOfBeingAbsorbedLogLossStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hadj : AdjacentCellsMeetStep 𝒮) : IterativeBoundStmt 𝒮 :=
  iterativeBound_of_steps 𝒮 h69 (AbelianIDLA.abelianIDLAAnyStartStep 𝒮) h28 hadj srwPathStep
    (fieldSigmaMeasurableStep 𝒮) IterativeBound.quenchedIterationStep

/-- **Lemma 6.10** from the drafted Lemma 6.9 (which implies its E-A10 (b) form). -/
theorem iterativeBound' (𝒮 : SpaceFillingSLEModel) (h69 : ChanceOfBeingAbsorbedStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hadj : AdjacentCellsMeetStep 𝒮) : IterativeBoundStmt 𝒮 :=
  iterativeBound 𝒮 h69.logLoss h28 hadj

end MatedCRT
