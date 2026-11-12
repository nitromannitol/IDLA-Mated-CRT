import MatedCRT.FirstPass.Derived.CoreOfRunningMinTail
import MatedCRT.FirstPass.Derived.SimilarityTransferDerived
import MatedCRT.FirstPass.Derived.ConeWholePlaneFieldLaw
import MatedCRT.FirstPass.Closure.AppendixBRewire

/-!
# The core of the reference model: similarity transfer and occupation identity supplied

Two more hypotheses of `CertifiedReferenceModelCore.of_runningMinTail` follow from the others or from smaller inputs:

* conjunct 17, the similarity transfer of the quantum cone and the space-filling curve (Duplantier-Miller-Sheffield
  arXiv:1409.7055 Proposition 4.13(i), Berestycki-Gwynne arXiv:2003.10320 Lemma 2.3), is
  `fpSimilarityTransferCorrected_of_law` from the normalized law of the curve (conjunct 1) and the scale invariance of
  the SLE predicate, the first component of the closure input (conjunct 2);
* conjunct 9, the occupation identity of the median-rescaled Liouville Brownian motion on the γ-quantum cone
  (Appendix B), is `frozenLBMGreenOccupationRescaled_of_fieldLaw` from the field-level law identity eq:gff on the unit
  disk, proved as `coneWholePlaneFieldLawStep_holds`, and the occupation identity `hGFF` of the clock of the field
  `h^ℂ - γ log|·|` with an independent planar Brownian motion, `h^ℂ` a whole-plane GFF.

`CertifiedReferenceModelCore.of_runningMinTail_law` drops conjunct 17; `CertifiedReferenceModelCore.of_runningMinTail_gff`
also replaces conjunct 9 by `hGFF`.
-/

open MeasureTheory Set Metric MatedCRTHarmonic.MatedCRT
open scoped Finset
open MatedCRT.KilledOccupation HarmonicBalls MarkovProcess

namespace MatedCRT.FirstPass.Derived

/-- **The core of the certified reference model without the similarity transfer among its inputs.** As
`CertifiedReferenceModelCore.of_runningMinTail`, conjunct 17 being `fpSimilarityTransferCorrected_of_law h1 h2.1`. -/
theorem CertifiedReferenceModelCore.of_runningMinTail_law {ν : ℝ → Measure MatedCRT.SLEPathCode}
    {𝒮 : MatedCRT.SpaceFillingSLEModel}
    (h1 : MatedCRT.HasNormalizedSLELaw 𝒮 ν) (h2 : MatedCRT.SLEModelClosureInput 𝒮)
    (h3 : MatedCRT.MepsScalingInput 𝒮) (h4 : MatedCRT.DegreeBoundInput 𝒮)
    (h9 : MatedCRT.FrozenLBMGreenOccupationRescaled 𝒮) (h10 : MatedCRT.HasReferenceEnvironments 𝒮)
    (h11 : MatedCRT.RandomWalkToLBMStmt 𝒮) (h12 : MatedCRT.GreenKernelUpperBoundStmt 𝒮)
    (h13 : MatedCRT.GreenKernelLowerBoundStmt 𝒮)
    (h15 : MatedCRT.FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h215 : MatedCRT.GreenFunctionCrudeBoundStmt 𝒮)
    (hEnv : MatedCRT.ConeEnvironmentScalingStep 𝒮)
    (hF6 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ C c : ℝ, 0 < c ∧ ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ →
      ∀ (i : Fin 2) (ε : ℝ), 0 < ε → ∀ (a : ℤ) (N : ℕ), 1 ≤ N → ∀ m : ℝ,
        μ {p | m < (#(MatedCRT.blockRunningMinCells ε (fun t => lrCoord i t p) (a + 1) (a + N)) : ℝ)} ≤
          ENNReal.ofReal (C * Real.exp (-(c * m / Real.sqrt N))) ∧
        μ {p | m < (#(MatedCRT.blockRunningMinCells ε
          (MatedCRT.blockReversal ε (fun t => lrCoord i t p) (a + 1) (a + N)) (a + 1) (a + N)) : ℝ)} ≤
          ENNReal.ofReal (C * Real.exp (-(c * m / Real.sqrt N)))) :
    MatedCRT.CertifiedReferenceModelCore ν 𝒮 :=
  CertifiedReferenceModelCore.of_runningMinTail h1 h2 h3 h4 h9 h10 h11 h12 h13 h15
    (fpSimilarityTransferCorrected_of_law h1 h2.1) h215 hEnv hF6

/-- **The core of the certified reference model from the occupation identity of the clock of the whole-plane GFF.**
As `CertifiedReferenceModelCore.of_runningMinTail_law`, conjunct 9 (Appendix B) being
`frozenLBMGreenOccupationRescaled_of_fieldLaw` with the proved field-level law identity eq:gff on the unit disk and the
occupation identity `hGFF` of the clock of `h^ℂ - γ log|·|`, `h^ℂ` a whole-plane GFF, with an independent planar
Brownian motion. -/
theorem CertifiedReferenceModelCore.of_runningMinTail_gff {ν : ℝ → Measure MatedCRT.SLEPathCode}
    {𝒮 : MatedCRT.SpaceFillingSLEModel}
    (h1 : MatedCRT.HasNormalizedSLELaw 𝒮 ν) (h2 : MatedCRT.SLEModelClosureInput 𝒮)
    (h3 : MatedCRT.MepsScalingInput 𝒮) (h4 : MatedCRT.DegreeBoundInput 𝒮)
    (h10 : MatedCRT.HasReferenceEnvironments 𝒮)
    (h11 : MatedCRT.RandomWalkToLBMStmt 𝒮) (h12 : MatedCRT.GreenKernelUpperBoundStmt 𝒮)
    (h13 : MatedCRT.GreenKernelLowerBoundStmt 𝒮)
    (h15 : MatedCRT.FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h215 : MatedCRT.GreenFunctionCrudeBoundStmt 𝒮)
    (hEnv : MatedCRT.ConeEnvironmentScalingStep 𝒮)
    (hF6 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ C c : ℝ, 0 < c ∧ ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ →
      ∀ (i : Fin 2) (ε : ℝ), 0 < ε → ∀ (a : ℤ) (N : ℕ), 1 ≤ N → ∀ m : ℝ,
        μ {p | m < (#(MatedCRT.blockRunningMinCells ε (fun t => lrCoord i t p) (a + 1) (a + N)) : ℝ)} ≤
          ENNReal.ofReal (C * Real.exp (-(c * m / Real.sqrt N))) ∧
        μ {p | m < (#(MatedCRT.blockRunningMinCells ε
          (MatedCRT.blockReversal ε (fun t => lrCoord i t p) (a + 1) (a + N)) (a + 1) (a + N)) : ℝ)} ≤
          ENNReal.ofReal (C * Real.exp (-(c * m / Real.sqrt N))))
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
  CertifiedReferenceModelCore.of_runningMinTail_law h1 h2 h3 h4
    (MatedCRT.frozenLBMGreenOccupationRescaled_of_fieldLaw
      MatedCRT.ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds hGFF 𝒮)
    h10 h11 h12 h13 h15 h215 hEnv hF6

end MatedCRT.FirstPass.Derived
