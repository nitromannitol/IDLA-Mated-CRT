import MatedCRT.FirstPass.Derived.EnvironmentScalingHolds
import MatedCRT.FirstPass.Derived.GreenKernelUpperOfReference
import MatedCRT.FirstPass.Derived.ResistanceBoundOfReference
import MatedCRT.FirstPass.Derived.DiscreteHolderOfReference

/-!
# Theorems 1.4 and 1.6 with the Green kernel bounds and the discrete Hölder estimate from mating rigidity

The counted forms `closed_1_4_lp_noSC_noSup_derivedInputs_envScaling` and
`closed_1_6_lp_noSC_noSup_derivedInputs_envScaling` bind the Green kernel upper bound (Lemma 2.15, Berestycki–Gwynne
2020 Lemma 5.4), the Green kernel lower bound (Lemma 2.16, Berestycki–Gwynne 2020 Lemma 4.4) and the corrected
discrete Hölder estimate (Lemma 3.2, Gwynne–Miller–Sheffield 2019 Theorem 3.9). For a model with a normalized
space-filling SLE law and valid reference environments, all three are theorems once a one-sided mating-rigid set `G`
of pairs of paths (`MatingRigidLEOn G`) is full for every `γ`-correlated two-sided Brownian law, `γ ∈ (0, 2)`:

* `greenKernelUpperBoundStmt_of_reference`, `greenKernelLowerBoundStmt_of_reference`,
  `frozenDiscreteHolderContinuityCorrected_of_reference` (with the cell size estimate `cellSizeEstimateStmt_holds`).

The forms below replace the binders `h12`, `h13`, `h15` by the rigidity pair `(hGnull, hG)`. Same conclusions.
-/

open MeasureTheory

namespace MatedCRT

open ProbabilityTheory Set Metric Finset _root_.MatedCRTHarmonic.MatedCRT
open _root_.MatedCRT.KilledOccupation _root_.HarmonicBalls _root_.MarkovProcess

section CountedRigidity

/-- **Theorem 1.4** in the counted form `closed_1_4_lp_noSC_noSup_derivedInputs_envScaling`, with the Green kernel
bounds (`h12`, `h13`) and the corrected discrete Hölder estimate (`h15`) derived from a one-sided mating-rigid set `G`
that is full for every `γ`-correlated two-sided Brownian law. Same conclusion. -/
theorem closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidity
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hlow : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → S.mεCdf ε (c₁ * ε⁻¹) < 1 / 2)
    (h10 : HasReferenceEnvironments 𝒮)
    (h11 : RandomWalkToLBMStmt 𝒮)
    {G : Set MatedCRTHarmonic.MatedCRT.Path2}
    (hGnull : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2,
      MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ → μ Gᶜ = 0)
    (hG : MatingRigidLEOn G)
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
  closed_1_4_lp_noSC_noSup_derivedInputs_envScaling ν h1 h2 hlow h10 h11
    (FirstPass.Derived.greenKernelUpperBoundStmt_of_reference h1 h10 hGnull hG)
    (FirstPass.Derived.greenKernelLowerBoundStmt_of_reference h1 h1 h10 hGnull hG)
    (FirstPass.Derived.frozenDiscreteHolderContinuityCorrected_of_reference h1 h10
      (fun γ hγ0 hγ2 => ⟨G, hGnull γ hγ0 hγ2, hG⟩) (FirstPass.Derived.cellSizeEstimateStmt_holds 𝒮))
    hGFF hscale

/-- **Theorem 1.6** in the counted form `closed_1_6_lp_noSC_noSup_derivedInputs_envScaling`, with the Green kernel
bounds (`h12`, `h13`) and the corrected discrete Hölder estimate (`h15`) derived from a one-sided mating-rigid set `G`
that is full for every `γ`-correlated two-sided Brownian law. Same conclusion. -/
theorem closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidity
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hlow : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → S.mεCdf ε (c₁ * ε⁻¹) < 1 / 2)
    (h10 : HasReferenceEnvironments 𝒮)
    (h11 : RandomWalkToLBMStmt 𝒮)
    {G : Set MatedCRTHarmonic.MatedCRT.Path2}
    (hGnull : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2,
      MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ → μ Gᶜ = 0)
    (hG : MatingRigidLEOn G)
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
  closed_1_6_lp_noSC_noSup_derivedInputs_envScaling ν h1 h2 hlow h10 h11
    (FirstPass.Derived.greenKernelUpperBoundStmt_of_reference h1 h10 hGnull hG)
    (FirstPass.Derived.greenKernelLowerBoundStmt_of_reference h1 h1 h10 hGnull hG)
    (FirstPass.Derived.frozenDiscreteHolderContinuityCorrected_of_reference h1 h10
      (fun γ hγ0 hγ2 => ⟨G, hGnull γ hγ0 hγ2, hG⟩) (FirstPass.Derived.cellSizeEstimateStmt_holds 𝒮))
    hGFF hscale

end CountedRigidity

end MatedCRT
