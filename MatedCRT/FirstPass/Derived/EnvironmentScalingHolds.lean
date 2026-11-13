import MatedCRT.FirstPass.Derived.RescaledMatingOfTreesFromLift
import MatedCRT.FirstPass.Derived.RescaledConeFieldDecoded
import MatedCRT.FirstPass.Derived.CoreGffLowerDerived
import MatedCRT.FirstPass.Derived.CoreExitTimeFromBG20
import MatedCRT.FirstPass.Derived.ConeDilationRatioHolds
import MatedCRT.FirstPass.Closure.Final22
import LatticeProb.LQG.MatingOfTreesCouplingRescale

/-!
# The environment scaling under space-filling SLE, from the quantum cone scaling input

* `rescaledMatingOfTreesStep_holds`: the mating-of-trees step `RescaledMatingOfTreesStep 𝒮` for every model, from
  `rescaledMatingOfTreesStep_of_lift` and the Lattice-Probability theorem
  `IsCouplingData.of_map_eq_of_ae_coneRescale` (Brownian rescalings of a mating-of-trees coupling with its law are
  mating-of-trees couplings).
* `lqgMeasurePropertiesStmt_of_scaling`: Fact 2.2 from `QuantumConeScalingInput` alone (volume growth and the
  non-dyadic dilations are theorems).
* `coneEnvironmentScalingUnderSLE_of_scaling`: `ConeEnvironmentScalingUnderSLE 𝒮` (eq:scale-invariance-of-field-and-eta)
  from `QuantumConeScalingInput`.
* `closed_1_4_lp_noSC_noSup_derivedInputs_envScaling`, `closed_1_6_lp_noSC_noSup_derivedInputs_envScaling`: the
  counted forms of Theorems 1.4 and 1.6 without the environment scaling binder.
-/

open MeasureTheory

namespace MatedCRT

/-- **The rescaled mating-of-trees step holds for every model.** -/
theorem rescaledMatingOfTreesStep_holds (𝒮 : SpaceFillingSLEModel) : RescaledMatingOfTreesStep 𝒮 := by
  refine rescaledMatingOfTreesStep_of_lift 𝒮 ?_
  intro γ hγ hγ2 b hb Ω _ P V V' hV hC hV' hlaw hae
  have h := ae_coneRescale_of_coneTriple_eq hae
  exact hC.of_map_eq_of_ae_coneRescale hγ hγ2 hV hV' hlaw hb (ae_of_all _ h.1) h.2.1 h.2.2

/-- **Fact 2.2 from the quantum cone scaling input.** -/
theorem lqgMeasurePropertiesStmt_of_scaling (hscale : QuantumConeScalingInput) :
    LQGMeasurePropertiesStmt :=
  LQGMeasure.lqgMeasureProperties_of_volumeGrowth FirstPass.Derived.volumeGrowthStmt_holds
    FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds coneCircleAverageLocalityStep_proved
    (LQGMeasure.coneFieldScalingStep_proved_radial hscale) (coneScaleRadiusPosStep_of_input hscale)

/-- **Environment scaling under space-filling SLE from the quantum cone scaling input.** -/
theorem coneEnvironmentScalingUnderSLE_of_scaling (𝒮 : SpaceFillingSLEModel)
    (hscale : QuantumConeScalingInput) : ConeEnvironmentScalingUnderSLE 𝒮 :=
  FirstPass.Derived.coneEnvironmentScalingUnderSLE_of_mating 𝒮 hscale
    (lqgMeasurePropertiesStmt_of_scaling hscale) (rescaledMatingOfTreesStep_holds 𝒮)

section CountedEnvScaling

open ProbabilityTheory Set Metric Finset _root_.MatedCRTHarmonic.MatedCRT
open _root_.MatedCRT.KilledOccupation _root_.HarmonicBalls _root_.MarkovProcess

/-- The counted form `closed_1_4_lp_noSC_noSup_derivedInputs_reducedCore` of Theorem 1.4 with the environment
scaling under space-filling SLE (eq:scale-invariance-of-field-and-eta) supplied by
`coneEnvironmentScalingUnderSLE_of_scaling` from the quantum cone scaling input. Same conclusion. -/
theorem closed_1_4_lp_noSC_noSup_derivedInputs_envScaling
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hlow : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → S.mεCdf ε (c₁ * ε⁻¹) < 1 / 2)
    (h10 : HasReferenceEnvironments 𝒮)
    (h11 : RandomWalkToLBMStmt 𝒮) (h12 : GreenKernelUpperBoundStmt 𝒮)
    (h13 : GreenKernelLowerBoundStmt 𝒮)
    (h15 : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (hGFF : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (r : ℝ) (z y : ℂ), 0 < r →
      ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hc : Ω' → ℝ → ℂ → ℝ), IsProbabilityMeasure P' → HarmonicBalls.IsWholePlaneGFF P' hC' hc →
      ∀ n : ℕ → ℕ, StrictMono n → HarmonicBalls.dyadicScale (n 0) < 1 - ρ →
      (∀ k : ℕ, clockAnnealedLaw P' (fun ω' => fieldCircleAverage γ (hc ω')) y
        {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) <
          clockGapFun γ (exitNN z r) (HarmonicBalls.dyadicScale (n k))
            (HarmonicBalls.dyadicScale (n (k + 1))) x}
          ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) →
      ∀ C : Set (Set ℂ), C.Countable → (∀ A ∈ C, MeasurableSet A ∧ A ⊆ ball z r) →
        ∀ᵐ ω' ∂P', clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω' ∈
          occupationAgreementEvent
            (limClockOccupationMeasure γ (fun k => HarmonicBalls.dyadicScale (n k)) z r
              (planarBrownianMotion y))
            (gmcGreenMeasure γ ρ ((1 + ρ) / 2) z y r) (ball z r) C)
    (hscale : QuantumConeScalingInput) :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_lp_noSC_noSup_derivedInputs_reducedCore ν h1 h2 hlow h10 h11 h12 h13 h15 hGFF hscale
    (coneEnvironmentScalingUnderSLE_of_scaling 𝒮 hscale)

/-- The counted form `closed_1_6_lp_noSC_noSup_derivedInputs_reducedCore` of Theorem 1.6 with the environment
scaling under space-filling SLE (eq:scale-invariance-of-field-and-eta) supplied by
`coneEnvironmentScalingUnderSLE_of_scaling` from the quantum cone scaling input. Same conclusion. -/
theorem closed_1_6_lp_noSC_noSup_derivedInputs_envScaling
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hlow : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → S.mεCdf ε (c₁ * ε⁻¹) < 1 / 2)
    (h10 : HasReferenceEnvironments 𝒮)
    (h11 : RandomWalkToLBMStmt 𝒮) (h12 : GreenKernelUpperBoundStmt 𝒮)
    (h13 : GreenKernelLowerBoundStmt 𝒮)
    (h15 : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (hGFF : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (r : ℝ) (z y : ℂ), 0 < r →
      ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hc : Ω' → ℝ → ℂ → ℝ), IsProbabilityMeasure P' → HarmonicBalls.IsWholePlaneGFF P' hC' hc →
      ∀ n : ℕ → ℕ, StrictMono n → HarmonicBalls.dyadicScale (n 0) < 1 - ρ →
      (∀ k : ℕ, clockAnnealedLaw P' (fun ω' => fieldCircleAverage γ (hc ω')) y
        {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) <
          clockGapFun γ (exitNN z r) (HarmonicBalls.dyadicScale (n k))
            (HarmonicBalls.dyadicScale (n (k + 1))) x}
          ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) →
      ∀ C : Set (Set ℂ), C.Countable → (∀ A ∈ C, MeasurableSet A ∧ A ⊆ ball z r) →
        ∀ᵐ ω' ∂P', clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω' ∈
          occupationAgreementEvent
            (limClockOccupationMeasure γ (fun k => HarmonicBalls.dyadicScale (n k)) z r
              (planarBrownianMotion y))
            (gmcGreenMeasure γ ρ ((1 + ρ) / 2) z y r) (ball z r) C)
    (hscale : QuantumConeScalingInput) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_lp_noSC_noSup_derivedInputs_reducedCore ν h1 h2 hlow h10 h11 h12 h13 h15 hGFF hscale
    (coneEnvironmentScalingUnderSLE_of_scaling 𝒮 hscale)

end CountedEnvScaling

end MatedCRT
