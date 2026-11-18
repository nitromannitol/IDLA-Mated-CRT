import MatedCRT.FirstPass.Derived.RandomWalkToLBMStmtOfConeInputs
import MatedCRT.FirstPass.Derived.ValidApproximantBallBound

/-!
# Convergence of the embedded random walk to Liouville Brownian motion, continuity input proved

`randomWalkToLBMStmt_of_cone_inputs` with its continuity binder `hL4` (almost surely, the law of the
Liouville Brownian path from `z` is defined for every `z` and continuous in `z`; Berestycki–Gwynne
(2020), Proposition 6.1 and Lemma 7.17) supplied by `lbmLawContinuity_of_isValid`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal

namespace MatedCRT

/-- **Random walk to Liouville Brownian motion, continuity input proved.** The binders are those of
`randomWalkToLBMStmt_of_cone_inputs` except `hL4`, which holds for every valid environment
(`FirstPass.Derived.lbmLawContinuity_of_isValid`). -/
theorem randomWalkToLBMStmt_of_cone_inputs_derived {𝒮 : SpaceFillingSLEModel}
    (hEnvS : ConeEnvironmentScalingStep 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    {ν : ℝ → Measure SLEPathCode} (hν : HasNormalizedSLELaw 𝒮 ν) (href : HasReferenceEnvironments 𝒮)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    (hBG : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ S₀ : MatedCRTEnv ℝ, S₀.IsValid 𝒮 γ →
      ∀ H₀ : ℝ → LQGMetric.DistC, Measurable H₀ → (∀ᵐ ω ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC ω φ = H₀ ω φ) →
      ∀ η₀ : ℝ → C(ℝ, ℂ), Measurable η₀ → (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) →
      ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun ε => S₀.P {ω | ∃ z ∈ K,
        δ ≤ FirstPass.Derived.pathLevyProkhorovEDist (FirstPass.Derived.selCellLaw S₀ η₀ ε ω z)
          (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H₀ ω)) z)}) (𝓝[>] 0) (𝓝 0)) :
    RandomWalkToLBMStmt 𝒮 :=
  randomWalkToLBMStmt_of_cone_inputs hEnvS hN4 hν href hU
    FirstPass.Derived.lbmLawContinuity_of_isValid hBG

end MatedCRT
