import MatedCRT.FirstPass.Derived.CoreRigidityInputsRationalDescent
import LatticeProb.Prob.CorrelatedBMExcursionCount

/-!
# Theorems 1.4 and 1.6 with the excursion-count formula at rational times derived

The forms `closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent` and
`closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent` bind three almost sure
properties of every `γ`-correlated two-sided Brownian law. The first of them, `hexc`, is Lévy's excursion-count
formula at a fixed rational time `q`: for each coordinate `X`, almost surely, for every `t ≥ q` the number of
excursions of `X` above its running minimum from `q` inside `[q, t]` of length larger than `ε`, multiplied by
`√(π ε / 2)`, tends to `X q - min_{[q, t]} X` as `ε → 0⁺`, and the same holds backward from `q` on `[t, q]`. It holds
for every such law: the recentred increments after `q`, and the time-reversed increments before `q`, form standard
Brownian motions, for which the formula is Lévy's description of the running minimum as the limit of the normalized
number of long excursions (`LatticeProb.CorrelatedBM.ae_excursionCount_lrCoord`).

The forms below drop `hexc`. Every other hypothesis and the conclusions are unchanged.

## Main statements

* `MatedCRT.closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount`,
  `MatedCRT.closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount`
-/

open MeasureTheory

namespace MatedCRT

open Set Filter Topology Metric _root_.MatedCRTHarmonic.MatedCRT
open _root_.MatedCRT.KilledOccupation _root_.HarmonicBalls _root_.MarkovProcess
open scoped NNReal ENNReal

section CountedRigidityInputsExcursionCount

/-- **Theorem 1.4** in the counted form
`closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent`, with Lévy's excursion-count
formula for the coordinates of the `γ`-correlated two-sided Brownian motion at rational times derived
(`LatticeProb.CorrelatedBM.ae_excursionCount_lrCoord`). Same conclusion. -/
theorem closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (h11 : RandomWalkToLBMStmt 𝒮)
    (hNC : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ →
      ∀ᵐ ω ∂μ, LatticeProb.CorrelatedBM.NoCommonWeakContourPair ω)
    (hZ3 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ →
      ∀ᵐ ω ∂μ, (matingTriplePoints ω).Countable ∨ ∃ d : ℝ≥0∞, dimH (matingTriplePoints ω) ≤ d ∧ d < 1 / 2)
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
  closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent ν h1 h2 hN4 h10 h11
    (fun _ _ _ _ hμ => LatticeProb.CorrelatedBM.ae_excursionCount_lrCoord hμ) hNC hZ3 hGFF hscale

/-- **Theorem 1.6** in the counted form
`closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent`, with Lévy's excursion-count
formula for the coordinates of the `γ`-correlated two-sided Brownian motion at rational times derived
(`LatticeProb.CorrelatedBM.ae_excursionCount_lrCoord`). Same conclusion. -/
theorem closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (h11 : RandomWalkToLBMStmt 𝒮)
    (hNC : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ →
      ∀ᵐ ω ∂μ, LatticeProb.CorrelatedBM.NoCommonWeakContourPair ω)
    (hZ3 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ →
      ∀ᵐ ω ∂μ, (matingTriplePoints ω).Countable ∨ ∃ d : ℝ≥0∞, dimH (matingTriplePoints ω) ≤ d ∧ d < 1 / 2)
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
  closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent ν h1 h2 hN4 h10 h11
    (fun _ _ _ _ hμ => LatticeProb.CorrelatedBM.ae_excursionCount_lrCoord hμ) hNC hZ3 hGFF hscale

end CountedRigidityInputsExcursionCount

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount
#print axioms MatedCRT.closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount
