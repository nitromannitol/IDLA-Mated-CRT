import MatedCRT.FirstPass.Derived.CoreGffDegreeDerived
import MatedCRT.FirstPass.Derived.MepsScalingOfLower
import MatedCRT.FirstPass.Derived.GreenFunctionCrudeBoundHolds

/-!
# The reference-model core without the crude Green function bound and with the lower half of (1.8)

`CertifiedReferenceModelCore.of_runningMinTail_gff_degree_derived` takes, among its hypotheses, the crude Green
function bound (Lemma 2.15, Berestycki-Gwynne Lemma 5.6) and the scaling `C⁻¹ ε⁻¹ ≤ m_ε ≤ C ε⁻¹` of the
expected exit time (conjunct 3, Berestycki-Gwynne eq. (1.8)). The crude bound holds for every model
(`greenFunctionCrudeBoundStmt_holds`), and, given it, the cell size estimate (`cellSizeEstimateStmt_holds`), the block
degree estimate (Berestycki-Gwynne (A.43), `hblock_of_degreeBound` with `degreeBoundInput_holds`) and the Green
kernel upper bound (Lemma 5.4), the scaling of `m_ε` reduces to its lower half `F_ε(c₁ ε⁻¹) < 1/2`
(`mepsScalingInput_of_lower_of_blockDegree`).

Since the environment scaling step is the closure statement `ConeEnvironmentScalingUnderSLE` evaluated at the three
closure properties of `SLEModelClosureInput`, the counted forms of Theorems 1.4 and 1.6 follow from the conjuncts
of the core that are not yet theorems, the lower half of (1.8), the whole-plane GFF occupation input, the quantum
cone scaling input and `ConeEnvironmentScalingUnderSLE`.

## Main statements

* `MatedCRT.FirstPass.Derived.CertifiedReferenceModelCore.of_gff_lower_derived`
* `MatedCRT.closed_1_4_lp_noSC_noSup_derivedInputs_reducedCore`,
  `MatedCRT.closed_1_6_lp_noSC_noSup_derivedInputs_reducedCore`
-/

open MeasureTheory ProbabilityTheory Set Metric Finset MatedCRTHarmonic.MatedCRT
open MatedCRT.KilledOccupation HarmonicBalls MarkovProcess
open scoped NNReal

namespace MatedCRT.FirstPass.Derived

/-- **The certified reference model core from the lower half of (1.8).**
`CertifiedReferenceModelCore.of_runningMinTail_gff_degree_derived` with the crude Green function bound supplied by
`greenFunctionCrudeBoundStmt_holds` and conjunct 3 (`MepsScalingInput`) by
`mepsScalingInput_of_lower_of_blockDegree` from the lower half `F_ε(c₁ ε⁻¹) < 1/2` of the distribution bounds of the
exit time; the cell size estimate and the block degree estimate there are `cellSizeEstimateStmt_holds` and
`hblock_of_degreeBound degreeBoundInput_holds`. -/
theorem CertifiedReferenceModelCore.of_gff_lower_derived
    {ν : ℝ → Measure MatedCRT.SLEPathCode} {𝒮 : MatedCRT.SpaceFillingSLEModel}
    (h1 : MatedCRT.HasNormalizedSLELaw 𝒮 ν) (h2 : MatedCRT.SLEModelClosureInput 𝒮)
    (hlow : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRT.MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → S.mεCdf ε (c₁ * ε⁻¹) < 1 / 2)
    (h10 : MatedCRT.HasReferenceEnvironments 𝒮)
    (h11 : MatedCRT.RandomWalkToLBMStmt 𝒮) (h12 : MatedCRT.GreenKernelUpperBoundStmt 𝒮)
    (h13 : MatedCRT.GreenKernelLowerBoundStmt 𝒮)
    (h15 : MatedCRT.FrozenDiscreteHolderContinuityCorrected 𝒮)
    (hEnv : MatedCRT.ConeEnvironmentScalingStep 𝒮)
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
            (gmcGreenMeasure γ ρ ((1 + ρ) / 2) z y r) (ball z r) C) :
    MatedCRT.CertifiedReferenceModelCore ν 𝒮 :=
  CertifiedReferenceModelCore.of_runningMinTail_gff_degree_derived h1 h2
    (MatedCRT.mepsScalingInput_of_lower_of_blockDegree h12 (MatedCRT.greenFunctionCrudeBoundStmt_holds 𝒮)
      (cellSizeEstimateStmt_holds 𝒮) (hblock_of_degreeBound (MatedCRT.degreeBoundInput_holds 𝒮)) hlow)
    h10 h11 h12 h13 h15 (MatedCRT.greenFunctionCrudeBoundStmt_holds 𝒮) hEnv hGFF

end MatedCRT.FirstPass.Derived

namespace MatedCRT

/-- The counted form `closed_1_4_lp_noSC_noSup_derivedInputs_crude` of Theorem 1.4 with the core
`hcore : CertifiedReferenceModelCore ν 𝒮` supplied by `CertifiedReferenceModelCore.of_gff_lower_derived`, whose
environment scaling step is `hEnvS` at the three closure properties of `h2`. Same conclusion. -/
theorem closed_1_4_lp_noSC_noSup_derivedInputs_reducedCore
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
    (hscale : QuantumConeScalingInput)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮) :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_lp_noSC_noSup_derivedInputs_crude ν
    (FirstPass.Derived.CertifiedReferenceModelCore.of_gff_lower_derived h1 h2 hlow h10 h11 h12 h13 h15
      (hEnvS h2.1 h2.2.1 h2.2.2) hGFF)
    hscale hEnvS

/-- The counted form `closed_1_6_lp_noSC_noSup_derivedInputs_crude` of Theorem 1.6 with the core
`hcore : CertifiedReferenceModelCore ν 𝒮` supplied by `CertifiedReferenceModelCore.of_gff_lower_derived`, whose
environment scaling step is `hEnvS` at the three closure properties of `h2`. Same conclusion. -/
theorem closed_1_6_lp_noSC_noSup_derivedInputs_reducedCore
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
    (hscale : QuantumConeScalingInput)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_lp_noSC_noSup_derivedInputs_crude ν
    (FirstPass.Derived.CertifiedReferenceModelCore.of_gff_lower_derived h1 h2 hlow h10 h11 h12 h13 h15
      (hEnvS h2.1 h2.2.1 h2.2.2) hGFF)
    hscale hEnvS

end MatedCRT
