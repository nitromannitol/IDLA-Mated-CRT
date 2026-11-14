import MatedCRT.FirstPass.Derived.CoreGffLowerOfLemma69Rigidity
import MatedCRT.FirstPass.S6j.ExitTimeLowerTail

/-!
# Theorems 1.4 and 1.6 with BG20 Lemma 6.9 from the uniform-start invariance principle

The forms `closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidity_lemma69` and
`closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidity_lemma69` bind the estimate `(6.32)` of
Berestycki-Gwynne Lemma 6.9 (`h632`). It follows from the uniform-start form of the invariance principle for the
walk on the mated-CRT map, the named literature input `GMS21UniformStartInput`, by
`ExitTimeLowerTail.exitTimeLowerTail_of_uniformStart`. The forms below replace the binder `h632` by `hN4`.
Same conclusions.

## Main statements

* `MatedCRT.closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidity_uniformStart`,
  `MatedCRT.closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidity_uniformStart`
-/

open MeasureTheory Filter Topology

namespace MatedCRT

open ProbabilityTheory Set Metric Finset _root_.MatedCRTHarmonic.MatedCRT
open _root_.MatedCRT.KilledOccupation _root_.HarmonicBalls _root_.MarkovProcess

section CountedRigidityUniformStart

/-- **Theorem 1.4** in the counted form `closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidity`, with the
lower half of (1.8) derived from the Green kernel bounds given by the rigidity pair `(hGnull, hG)` and
Berestycki-Gwynne Lemma 6.9, the latter from the uniform-start invariance principle `hN4`
(`ExitTimeLowerTail.exitTimeLowerTail_of_uniformStart`). Same conclusion. -/
theorem closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidity_uniformStart
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
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
  closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidity_lemma69 ν h1 h2
    (ExitTimeLowerTail.exitTimeLowerTail_of_uniformStart hN4) h10 h11 hGnull hG hGFF hscale

/-- **Theorem 1.6** in the counted form `closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidity`, with the
lower half of (1.8) derived from the Green kernel bounds given by the rigidity pair `(hGnull, hG)` and
Berestycki-Gwynne Lemma 6.9, the latter from the uniform-start invariance principle `hN4`
(`ExitTimeLowerTail.exitTimeLowerTail_of_uniformStart`). Same conclusion. -/
theorem closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidity_uniformStart
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
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
  closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidity_lemma69 ν h1 h2
    (ExitTimeLowerTail.exitTimeLowerTail_of_uniformStart hN4) h10 h11 hGnull hG hGFF hscale

end CountedRigidityUniformStart

end MatedCRT
