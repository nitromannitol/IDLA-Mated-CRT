import MatedCRT.FirstPass.Derived.CoreGffLowerOfUniformStart
import MatedCRT.FirstPass.Derived.MatingRigidityAssembly

/-!
# Theorems 1.4 and 1.6 with the lower half of (1.8) and the mating rigidity pair both derived

Two reductions of the counted forms `closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidity` and
`closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidity` combined:

* the lower half `hlow` of Berestycki-Gwynne (1.8) follows from the Green kernel bounds given by the rigidity pair
  and from Berestycki-Gwynne Lemma 6.9, the latter from the uniform-start form of the invariance principle for the
  walk on the mated-CRT map (`GMS21UniformStartInput`, the forms `..._rigidity_uniformStart`);
* the rigidity pair `(G, hGnull, hG)` follows from four almost sure properties of the `γ`-correlated two-sided
  Brownian law, with `G` the rigidity set of the triple points of the mating relation (the forms
  `..._rigidityInputs`).

The forms below bind `hN4` in place of `hlow` and the four properties `hdesc`, `hexc`, `hNC`, `hZ3` in place of the
rigidity pair. Same conclusions.

## Main statements

* `MatedCRT.closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart`,
  `MatedCRT.closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart`
-/

open MeasureTheory

namespace MatedCRT

open Set Filter Topology Metric _root_.MatedCRTHarmonic.MatedCRT
open _root_.MatedCRT.KilledOccupation _root_.HarmonicBalls _root_.MarkovProcess
open scoped NNReal ENNReal

section CountedRigidityInputsUniformStart

/-- **Theorem 1.4** in the counted form `closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidity`, with
the lower half of (1.8) derived from Berestycki-Gwynne Lemma 6.9 and the uniform-start invariance principle `hN4`,
and the rigidity pair derived from the four almost sure properties `hdesc`, `hexc`, `hNC`, `hZ3` of every
`γ`-correlated two-sided Brownian law (`G` is the rigidity set of the triple points of the mating relation).
Same conclusion. -/
theorem closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (h11 : RandomWalkToLBMStmt 𝒮)
    (hdesc : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ → ∀ i : Fin 2, ∀ q : ℚ,
      ∀ᵐ ω ∂μ, (∀ u < (q : ℝ), ∃ w ∈ Ioo u (q : ℝ), lrCoord i w ω < lrCoord i q ω) ∧
        ∀ u, (q : ℝ) < u → ∃ w ∈ Ioo (q : ℝ) u, lrCoord i w ω < lrCoord i q ω)
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
  closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidity_uniformStart ν h1 h2 hN4 h10 h11
    (G := LatticeProb.CorrelatedBM.rigiditySet matingTriplePoints)
    (fun γ hγ0 hγ2 μ hμ => measure_compl_rigiditySet_matingTriplePoints_eq_zero hμ hγ0 hγ2
      (hdesc γ hγ0 hγ2 μ hμ) (hexc γ hγ0 hγ2 μ hμ) (hNC γ hγ0 hγ2 μ hμ) (hZ3 γ hγ0 hγ2 μ hμ))
    matingRigidLEOn_rigiditySet hGFF hscale

/-- **Theorem 1.6** in the counted form `closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidity`, with
the lower half of (1.8) derived from Berestycki-Gwynne Lemma 6.9 and the uniform-start invariance principle `hN4`,
and the rigidity pair derived from the four almost sure properties `hdesc`, `hexc`, `hNC`, `hZ3` of every
`γ`-correlated two-sided Brownian law (`G` is the rigidity set of the triple points of the mating relation).
Same conclusion. -/
theorem closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (h11 : RandomWalkToLBMStmt 𝒮)
    (hdesc : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ → ∀ i : Fin 2, ∀ q : ℚ,
      ∀ᵐ ω ∂μ, (∀ u < (q : ℝ), ∃ w ∈ Ioo u (q : ℝ), lrCoord i w ω < lrCoord i q ω) ∧
        ∀ u, (q : ℝ) < u → ∃ w ∈ Ioo (q : ℝ) u, lrCoord i w ω < lrCoord i q ω)
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
  closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidity_uniformStart ν h1 h2 hN4 h10 h11
    (G := LatticeProb.CorrelatedBM.rigiditySet matingTriplePoints)
    (fun γ hγ0 hγ2 μ hμ => measure_compl_rigiditySet_matingTriplePoints_eq_zero hμ hγ0 hγ2
      (hdesc γ hγ0 hγ2 μ hμ) (hexc γ hγ0 hγ2 μ hμ) (hNC γ hγ0 hγ2 μ hμ) (hZ3 γ hγ0 hγ2 μ hμ))
    matingRigidLEOn_rigiditySet hGFF hscale

end CountedRigidityInputsUniformStart

end MatedCRT
