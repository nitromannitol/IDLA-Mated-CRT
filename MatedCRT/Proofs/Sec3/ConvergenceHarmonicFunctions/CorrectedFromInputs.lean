import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.HolderApproximation
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.PointwiseAssembly

/-! # Corrected harmonic convergence from the closed-disc modulus -/

namespace MatedCRT

/-- The convergence part of corrected Lemma 3.6 follows from the existing
walk-to-LBM and cell-size inputs together with the closed-disc modulus. -/
theorem correctedHarmonicConvergence_of_modulus (𝒮 : SpaceFillingSLEModel)
    (h211 : RandomWalkToLBMStmt 𝒮) (hmeps : MepsScalingInput 𝒮)
    (hexc : BrownianOutwardExcursionAtExitStep) (hX : LBMPathFunctionalMeasurableStep 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hmod : CorrectedHarmonicModulusStep 𝒮) :
    CorrectedHarmonicConvergenceStmt 𝒮 :=
  correctedHarmonicConvergence_of_projectedExit_modulus 𝒮 h211 hexc hX
    (correctedProjectedExitCellStep_of_inputs 𝒮 h211 hmeps hexc hX h28) hmod

end MatedCRT
