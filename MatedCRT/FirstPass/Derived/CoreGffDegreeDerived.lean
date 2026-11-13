import MatedCRT.FirstPass.Derived.DegreeBoundOfLemma25Tail

/-!
# The reference-model core from the whole-plane GFF input without the degree bound

`CertifiedReferenceModelCore.of_runningMinTail_gff_derived` with the degree bound eq:degree-bound
(GMS19 Lemma 2.6) supplied by the theorem `degreeBoundInput_holds`.

## Main statements

* `MatedCRT.FirstPass.Derived.CertifiedReferenceModelCore.of_runningMinTail_gff_degree_derived`
-/

open MeasureTheory ProbabilityTheory Set Metric Finset MatedCRTHarmonic.MatedCRT
open MatedCRT.KilledOccupation HarmonicBalls MarkovProcess
open scoped NNReal

namespace MatedCRT.FirstPass.Derived

/-- `CertifiedReferenceModelCore.of_runningMinTail_gff_derived` with the degree bound supplied by
`degreeBoundInput_holds`. -/
theorem CertifiedReferenceModelCore.of_runningMinTail_gff_degree_derived
    {ν : ℝ → Measure MatedCRT.SLEPathCode} {𝒮 : MatedCRT.SpaceFillingSLEModel}
    (h1 : MatedCRT.HasNormalizedSLELaw 𝒮 ν) (h2 : MatedCRT.SLEModelClosureInput 𝒮)
    (h3 : MatedCRT.MepsScalingInput 𝒮)
    (h10 : MatedCRT.HasReferenceEnvironments 𝒮)
    (h11 : MatedCRT.RandomWalkToLBMStmt 𝒮) (h12 : MatedCRT.GreenKernelUpperBoundStmt 𝒮)
    (h13 : MatedCRT.GreenKernelLowerBoundStmt 𝒮)
    (h15 : MatedCRT.FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h215 : MatedCRT.GreenFunctionCrudeBoundStmt 𝒮)
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
  CertifiedReferenceModelCore.of_runningMinTail_gff_derived h1 h2 h3 (MatedCRT.degreeBoundInput_holds 𝒮) h10
    h11 h12 h13 h15 h215 hEnv hGFF

end MatedCRT.FirstPass.Derived
