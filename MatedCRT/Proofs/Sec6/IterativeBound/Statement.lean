import MatedCRT.Proofs.Sec6.IterativeBound.OfSteps
import MatedCRT.Proofs.Sec6.IterativeBound.Walk
import MatedCRT.Proofs.Sec6.IterativeBound.Quenched
import MatedCRT.Proofs.Sec6.IterativeBound.FieldSigma
import MatedCRT.Proofs.Sec6.AbelianIDLA.Statement
import MatedCRT.Proofs.Sec6.ChanceOfBeingAbsorbed.LogLoss
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.OfSteps

/-!
# Lemma 6.10 (lemma:iterative-bound, line 2694)

`iterativeBound`: Lemma 6.10 from Lemma 6.9 (in the E-A10 (b) form, `ChanceOfBeingAbsorbedLogLossStmt`), Lemma 2.8 and
the intersection of the cells of adjacent vertices (`AdjacentCellsMeetStep`, Definitions 1.1 = 1.2). The other steps are proved: Lemma 6.3 for arbitrary starting sites (`AbelianIDLA.abelianIDLAAnyStartStep`),
the walk path property (`srwPathStep`), the measurability of the field (`fieldSigmaMeasurableStep`, from
`IsQuantumCone.measurable_pairing`) and the quenched iteration (`IterativeBound.quenchedIterationStep`).

`iterativeBound_of_div` and `iterativeBound_of_inputs` connect Lemma 6.10 to Lemma 6.8 in its route (b) form
(`ConstantOrderLowerBoundDivLogStmt`) through proved links only: 6.8 (b) gives 6.7 (b) (`constantOrderLowerBoundLog`),
which gives 6.9 (b) (`chanceOfBeingAbsorbedLogLoss`); `AdjacentCellsMeetStep` follows from the almost sure form
`AdjacentCellsMeetAeStep` (`AdjacentCellsMeetAeStep.probTendsToOne`).
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

/-- The almost sure intersection of the cells of adjacent vertices (`AdjacentCellsMeetAeStep`, all `ε > 0`) gives
its form with probability tending to `1` on `V^ε(B_ρ)`. -/
theorem AdjacentCellsMeetAeStep.probTendsToOne {𝒮 : SpaceFillingSLEModel} (h : AdjacentCellsMeetAeStep 𝒮) :
    AdjacentCellsMeetStep 𝒮 := by
  intro γ hγ hγ2 ρ _ _ Ω _ S hS
  exact (probTendsToOne_of_ae (G := {ω | ∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
    (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty}) (h γ hγ hγ2 Ω S hS)).mono_pos
    fun ε hε ω hω a b _ hab => hω ε hε a b hab

/-- **Lemma 6.10** from Lemma 6.8 in its route (b) form, Lemmas 2.7, 2.8, 2.19, and `AdjacentCellsMeetAeStep`,
through Lemmas 6.7 and 6.9 in their route (b) forms. -/
theorem iterativeBound_of_div (𝒮 : SpaceFillingSLEModel) (h68 : ConstantOrderLowerBoundDivLogStmt 𝒮)
    (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮)
    (hcell : AdjacentCellsMeetAeStep 𝒮) : IterativeBoundStmt 𝒮 :=
  iterativeBound 𝒮 (chanceOfBeingAbsorbedLogLoss_of_div 𝒮 h68 h27 h28 h219 hcell) h28 hcell.probTendsToOne

/-- **Lemma 6.10** from the inputs of Lemma 6.8, route (b) (`constantOrderLowerBoundDiv_of_steps`): Lemmas 2.16,
2.7, 2.8, 2.9, 6.4, 2.18, 2.19, and the steps `GoodScaleEventMeasurableStep` (line 2505) and `AdjacentCellsMeetAeStep`
(Definitions 1.1 = 1.2). -/
theorem iterativeBound_of_inputs (𝒮 : SpaceFillingSLEModel)
    (h216 : GreenKernelLowerBoundStmt 𝒮) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h64 : GoodAnnulusPrevalenceStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮)
    (hmeas : GoodScaleEventMeasurableStep 𝒮) (hcell : AdjacentCellsMeetAeStep 𝒮) : IterativeBoundStmt 𝒮 :=
  iterativeBound_of_div 𝒮
    (constantOrderLowerBoundDiv_of_steps 𝒮 h216 h27 h28 h29 h64 h218 h219 hmeas hcell) h27 h28 h219 hcell

end MatedCRT
