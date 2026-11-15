import MatedCRT.FirstPass.Derived.RevuzOccupationCauchyPolar
import MatedCRT.FirstPass.Derived.QuantumConeScalingDerived

/-!
# Main convergence results with quantum cone scaling supplied

These forms of Theorems 1.4 and 1.6 use the quantum cone scaling theorem and retain the
remaining hypotheses of the corresponding convergence statements.
-/

open MeasureTheory

namespace MatedCRT

/-- Theorem 1.4 with quantum cone scaling supplied. -/
theorem closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount_cauchyGHM_revuz_polar_scaling
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (h11 : RandomWalkToLBMStmt 𝒮)
    (hGHM : GHMConeDimInput) :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount_cauchyGHM_revuz_polar
    ν h1 h2 hN4 h10 h11 hGHM FirstPass.Derived.quantumConeScalingInput_derived

/-- Theorem 1.6 with quantum cone scaling supplied. -/
theorem closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount_cauchyGHM_revuz_polar_scaling
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (h11 : RandomWalkToLBMStmt 𝒮)
    (hGHM : GHMConeDimInput) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount_cauchyGHM_revuz_polar
    ν h1 h2 hN4 h10 h11 hGHM FirstPass.Derived.quantumConeScalingInput_derived

end MatedCRT
