import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.CorrectedFromInputs
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.SameWalkAssembly

/-! # Corrected Lemma 3.6 from the separated same-walk rates -/

namespace MatedCRT

/-- The corrected lemma from the modulus and the explicit annealed and
pointwise same-walk assembly steps. -/
theorem correctedLemma36_of_modulus_assembly (𝒮 : SpaceFillingSLEModel)
    (h211 : RandomWalkToLBMStmt 𝒮) (hmeps : MepsScalingInput 𝒮)
    (hexc : BrownianOutwardExcursionAtExitStep) (hX : LBMPathFunctionalMeasurableStep 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hmod : CorrectedHarmonicModulusStep 𝒮)
    (hrate : UniformSameWalkAssemblyStep 𝒮) : CorrectedLemma36Stmt 𝒮 :=
  correctedLemma36_of_modulus_rate 𝒮 h211 hmeps hexc hX h28 hmod
    (correctedHarmonicSameWalkRate_of_assembly 𝒮 hrate)

end MatedCRT

#print axioms MatedCRT.correctedLemma36_of_modulus_assembly
