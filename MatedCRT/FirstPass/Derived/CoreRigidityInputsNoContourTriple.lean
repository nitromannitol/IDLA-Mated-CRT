import MatedCRT.FirstPass.Derived.CoreRigidityInputsExcursionCount
import MatedCRT.FirstPass.Derived.MatingTriplePointsAssembly
import LatticeProb.Prob.CorrelatedBMNoCommonContour
import LatticeProb.Prob.CorrelatedBMMixedTimes
import LatticeProb.Prob.CorrelatedBMConeTimes

/-!
# Theorems 1.4 and 1.6 with the no-common-contour and triple-point properties derived

The forms `closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount`
and `closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount` bind two
almost sure properties of every `γ`-correlated two-sided Brownian law `μ` (`0 < γ < 2`):

* `hNC`: almost surely no pair of weak contour points is common to the two coordinates
  (`LatticeProb.CorrelatedBM.NoCommonWeakContourPair`). It follows from the polarity of points for the planar Cauchy
  process (`LatticeProb.CorrelatedBM.CauchyPointPolarInput`, `LatticeProb.CorrelatedBM.hNC_of_cauchyPointPolar`).
* `hZ3`: almost surely the triple points of the mating relation form a countable set, or a set of Hausdorff dimension
  at most some `d < 1/2`. It follows from the Gwynne-Holden-Miller bound on the Hausdorff dimension of the cone triple
  points (`GHMConeDimInput`) together with the almost sure countability of the times of mixed type
  (`LatticeProb.CorrelatedBM.ae_countable_mixTimes`) and, for `γ ≤ √2`, of the forward and backward cone times
  (`LatticeProb.CorrelatedBM.ae_countable_coneTimes_of_le_sqrt_two`), by `hZ3_of_inputs`.

The forms below replace `hNC` by `CauchyPointPolarInput` and `hZ3` by `GHMConeDimInput`. Every other hypothesis and the
conclusions are unchanged.

## Main statements

* `MatedCRT.hZ3_of_GHM`: the triple-point dichotomy from `GHMConeDimInput`.
* `MatedCRT.closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount_cauchyGHM`,
  `MatedCRT.closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount_cauchyGHM`
-/

open MeasureTheory

namespace MatedCRT

open Set Filter Topology Metric _root_.MatedCRTHarmonic.MatedCRT
open _root_.MatedCRT.KilledOccupation _root_.HarmonicBalls _root_.MarkovProcess
open scoped NNReal ENNReal

section CountedRigidityInputsNoContourTriple

/-- **Triple points of the mating relation.** Under the Gwynne-Holden-Miller bound `GHMConeDimInput` on the Hausdorff
dimension of the cone triple points, for `0 < γ < 2` and every `γ`-correlated two-sided Brownian law `μ`, almost surely
the triple points of the mating relation form a countable set, or a set of Hausdorff dimension at most some `d < 1/2`.
The times of mixed type are almost surely countable (`LatticeProb.CorrelatedBM.ae_countable_mixTimes`), and so are the
forward and backward cone times for `γ ≤ √2` (`LatticeProb.CorrelatedBM.ae_countable_coneTimes_of_le_sqrt_two`). -/
theorem hZ3_of_GHM (hGHM : GHMConeDimInput) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ →
      ∀ᵐ ω ∂μ, (matingTriplePoints ω).Countable ∨ ∃ d : ℝ≥0∞, dimH (matingTriplePoints ω) ≤ d ∧ d < 1 / 2 :=
  hZ3_of_inputs hGHM
    (fun _ hγ0 hγ2 _ hμ => LatticeProb.CorrelatedBM.ae_countable_mixTimes hγ0 hγ2 hμ)
    (fun _ hγ0 hγ _ hμ => LatticeProb.CorrelatedBM.ae_countable_coneTimes_of_le_sqrt_two hγ0 hγ hμ)

/-- **Theorem 1.4** in the counted form
`closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount`, with the
absence of common weak contour pairs derived from the polarity of points for the planar Cauchy process
(`LatticeProb.CorrelatedBM.hNC_of_cauchyPointPolar`) and the triple-point dichotomy derived from the
Gwynne-Holden-Miller cone-dimension bound (`hZ3_of_GHM`). Same conclusion. -/
theorem closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount_cauchyGHM
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (h11 : RandomWalkToLBMStmt 𝒮)
    (hCP : LatticeProb.CorrelatedBM.CauchyPointPolarInput)
    (hGHM : GHMConeDimInput)
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
  closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount ν h1 h2 hN4
    h10 h11 (LatticeProb.CorrelatedBM.hNC_of_cauchyPointPolar hCP) (hZ3_of_GHM hGHM) hGFF hscale

/-- **Theorem 1.6** in the counted form
`closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount`, with the
absence of common weak contour pairs derived from the polarity of points for the planar Cauchy process
(`LatticeProb.CorrelatedBM.hNC_of_cauchyPointPolar`) and the triple-point dichotomy derived from the
Gwynne-Holden-Miller cone-dimension bound (`hZ3_of_GHM`). Same conclusion. -/
theorem closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount_cauchyGHM
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (h11 : RandomWalkToLBMStmt 𝒮)
    (hCP : LatticeProb.CorrelatedBM.CauchyPointPolarInput)
    (hGHM : GHMConeDimInput)
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
  closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount ν h1 h2 hN4
    h10 h11 (LatticeProb.CorrelatedBM.hNC_of_cauchyPointPolar hCP) (hZ3_of_GHM hGHM) hGFF hscale

end CountedRigidityInputsNoContourTriple

end MatedCRT
