import MatedCRT.FirstPass.Derived.MatingConeDimensionDerived
import MatedCRT.FirstPass.Derived.QuantumConeScalingMain

/-! # Main convergence results with the cone dimension bound supplied -/

open MeasureTheory

namespace MatedCRT

/-- Theorem 1.4 with the cone dimension bound supplied. -/
theorem closed_1_4_quantumConeScaling_coneDimension
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (h11 : RandomWalkToLBMStmt 𝒮) : ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount_cauchyGHM_revuz_polar_scaling
    ν h1 h2 hN4 h10 h11 ghmConeDimInput_derived

/-- Theorem 1.6 with the cone dimension bound supplied. -/
theorem closed_1_6_quantumConeScaling_coneDimension
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (h11 : RandomWalkToLBMStmt 𝒮) : ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount_cauchyGHM_revuz_polar_scaling
    ν h1 h2 hN4 h10 h11 ghmConeDimInput_derived

end MatedCRT
