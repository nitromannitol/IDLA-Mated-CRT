import MatedCRT.FirstPass.Derived.CoreRigidityInputsUniformStart
import LatticeProb.Prob.CorrelatedBMRationalDescent

/-!
# Theorems 1.4 and 1.6 with the immediate descent at rational times derived

The forms `closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart` and
`closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart` bind four almost sure properties
of every `γ`-correlated two-sided Brownian law. The first of them, `hdesc` (for a fixed coordinate and a fixed
rational time `q`, the coordinate path takes values strictly below its value at `q` at times arbitrarily close
to `q`, on both sides), holds for every such law: after `q` the recentred increments form a standard Brownian
motion, before `q` so do the time-reversed increments, and a standard Brownian motion takes negative values at
arbitrarily small positive times by Blumenthal's zero-one law (`LatticeProb.CorrelatedBM.ae_rat_descends`).

The forms below drop `hdesc`. Every other hypothesis and the conclusions are unchanged.

## Main statements

* `MatedCRT.closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent`,
  `MatedCRT.closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent`
-/

open MeasureTheory

namespace MatedCRT

open Set Filter Topology Metric _root_.MatedCRTHarmonic.MatedCRT
open _root_.MatedCRT.KilledOccupation _root_.HarmonicBalls _root_.MarkovProcess
open scoped NNReal ENNReal

section CountedRigidityInputsRationalDescent

/-- **Theorem 1.4** in the counted form
`closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart`, with the immediate descent of the
coordinates of the `γ`-correlated two-sided Brownian motion at rational times derived
(`LatticeProb.CorrelatedBM.ae_rat_descends`). Same conclusion. -/
theorem closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (h11 : RandomWalkToLBMStmt 𝒮)
    (hexc : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ → ∀ i : Fin 2, ∀ q : ℚ,
      ∀ᵐ ω ∂μ, (∀ t, (q : ℝ) ≤ t → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
        (LatticeProb.LadderSet.excursionCount (LatticeProb.LadderSet.forwardLadderSet (fun s => lrCoord i s ω) q) q t ε : ℝ))
          (𝓝[>] 0) (𝓝 (lrCoord i q ω - sInf ((fun s => lrCoord i s ω) '' Icc (q : ℝ) t)))) ∧
      ∀ t, t ≤ (q : ℝ) → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
        (LatticeProb.LadderSet.excursionCount (LatticeProb.LadderSet.backwardLadderSet (fun s => lrCoord i s ω) q) t q ε : ℝ))
          (𝓝[>] 0) (𝓝 (lrCoord i q ω - sInf ((fun s => lrCoord i s ω) '' Icc t (q : ℝ)))))
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
  closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart ν h1 h2 hN4 h10 h11
    (fun _ _ _ _ hμ i q => LatticeProb.CorrelatedBM.ae_rat_descends hμ i q) hexc hNC hZ3 hGFF hscale

/-- **Theorem 1.6** in the counted form
`closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart`, with the immediate descent of the
coordinates of the `γ`-correlated two-sided Brownian motion at rational times derived
(`LatticeProb.CorrelatedBM.ae_rat_descends`). Same conclusion. -/
theorem closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (h11 : RandomWalkToLBMStmt 𝒮)
    (hexc : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ → ∀ i : Fin 2, ∀ q : ℚ,
      ∀ᵐ ω ∂μ, (∀ t, (q : ℝ) ≤ t → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
        (LatticeProb.LadderSet.excursionCount (LatticeProb.LadderSet.forwardLadderSet (fun s => lrCoord i s ω) q) q t ε : ℝ))
          (𝓝[>] 0) (𝓝 (lrCoord i q ω - sInf ((fun s => lrCoord i s ω) '' Icc (q : ℝ) t)))) ∧
      ∀ t, t ≤ (q : ℝ) → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
        (LatticeProb.LadderSet.excursionCount (LatticeProb.LadderSet.backwardLadderSet (fun s => lrCoord i s ω) q) t q ε : ℝ))
          (𝓝[>] 0) (𝓝 (lrCoord i q ω - sInf ((fun s => lrCoord i s ω) '' Icc t (q : ℝ)))))
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
  closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart ν h1 h2 hN4 h10 h11
    (fun _ _ _ _ hμ i q => LatticeProb.CorrelatedBM.ae_rat_descends hμ i q) hexc hNC hZ3 hGFF hscale

end CountedRigidityInputsRationalDescent

end MatedCRT
