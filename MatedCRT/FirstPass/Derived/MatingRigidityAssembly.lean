import MatedCRT.FirstPass.Derived.EnvironmentScalingRigidity
import MatedCRT.FirstPass.Derived.MatingTriplePoints
import LatticeProb.Prob.CorrelatedBMRegularPaths

/-!
# One-sided mating rigidity from the regularity of correlated Brownian paths

The counted forms `closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidity` and
`closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidity` bind a set `G` of pairs of paths that is one-sided
mating-rigid (`MatingRigidLEOn G`) and full for every `γ`-correlated two-sided Brownian law. Here `G` is the
rigidity set of the triple points of the mating relation (`LatticeProb.CorrelatedBM.rigiditySet matingTriplePoints`):
the regular coordinate pairs without a common weak contour pair whose triple points form a countable set or a set of
Hausdorff dimension `< 1/2`.

* `matingRigidLEOn_rigiditySet`: this set is one-sided mating-rigid, with no further input. If the mating relation
  of `b` is contained in that of `b'`, every straddling pair of a coordinate of `b` with a rational anchor and its
  left time off the triple points of `b'` is a direct identification of `b'` (`MatingTriplePoints`), and the contour
  rigidity of regular pairs (`LatticeProb.CorrelatedBM.eq_or_swap_of_mem_rigiditySet`) gives `b' = b` up to the swap.
* `measure_compl_rigiditySet_matingTriplePoints_eq_zero`: the set is full for a `γ`-correlated Brownian law, given
  four almost sure properties of the law: descent on both sides of each rational time (`hdesc`), Lévy's excursion
  count formula for the running minimum at each rational anchor (`hexc`), no common weak contour pair of the two
  coordinates, that is no cone excursion of the pair returning to its apex (`hNC`), and the size bound for the
  triple points of the mating relation (`hZ3`: countable for `γ ≤ √2`, Hausdorff dimension at most `1 - 2/γ²` for
  `γ > √2`).
* `exists_matingRigidLEOn_full`: the rigidity pair `(G, hGnull, hG)` from these four properties.
* `closed_1_4_..._envScaling_rigidityInputs`, `closed_1_6_..._envScaling_rigidityInputs`: the counted forms with the
  rigidity pair replaced by the four properties. Same conclusions.
-/

open MeasureTheory

namespace MatedCRT

open Set Filter Topology Metric _root_.MatedCRTHarmonic.MatedCRT
open _root_.MatedCRT.KilledOccupation _root_.HarmonicBalls _root_.MarkovProcess
open scoped NNReal ENNReal

/-- **The rigidity set of the triple points is one-sided mating-rigid.** For pairs `b, b'` in the rigidity set of
`matingTriplePoints`, if the mating relation of `b` is contained in that of `b'`, then `b' = b` or `b'` is `b` with
its two coordinates exchanged. -/
theorem matingRigidLEOn_rigiditySet :
    MatingRigidLEOn (LatticeProb.CorrelatedBM.rigiditySet matingTriplePoints) :=
  fun _ hb _ hb' hle => LatticeProb.CorrelatedBM.eq_or_swap_of_mem_rigiditySet hb hb'
    fun i w _ => forall_directRel_straddle_of_not_mem_matingTriplePoints i hle (hb.1.1 i).low w

/-- **The rigidity set of the triple points is full** for a `γ`-correlated two-sided Brownian law `μ`, `0 < γ < 2`,
as soon as, `μ`-almost surely: each coordinate takes values below its value at each rational time on both sides of
it (`hdesc`); at each rational anchor and in both time directions, the drop of the running minimum is the limit of
`√(π ε / 2)` times the number of excursions of diameter `> ε` above the running minimum (`hexc`); the two
coordinates have no common weak contour pair (`hNC`); and the triple points of the mating relation form a countable
set or a set of Hausdorff dimension `< 1/2` (`hZ3`). -/
theorem measure_compl_rigiditySet_matingTriplePoints_eq_zero {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hdesc : ∀ i : Fin 2, ∀ q : ℚ, ∀ᵐ ω ∂μ,
      (∀ u < (q : ℝ), ∃ w ∈ Ioo u (q : ℝ), lrCoord i w ω < lrCoord i q ω) ∧
        ∀ u, (q : ℝ) < u → ∃ w ∈ Ioo (q : ℝ) u, lrCoord i w ω < lrCoord i q ω)
    (hexc : ∀ i : Fin 2, ∀ q : ℚ, ∀ᵐ ω ∂μ,
      (∀ t, (q : ℝ) ≤ t → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
        (LatticeProb.LadderSet.excursionCount (LatticeProb.LadderSet.forwardLadderSet (fun s => lrCoord i s ω) q) q t ε : ℝ))
          (𝓝[>] 0) (𝓝 (lrCoord i q ω - sInf ((fun s => lrCoord i s ω) '' Icc (q : ℝ) t)))) ∧
      ∀ t, t ≤ (q : ℝ) → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
        (LatticeProb.LadderSet.excursionCount (LatticeProb.LadderSet.backwardLadderSet (fun s => lrCoord i s ω) q) t q ε : ℝ))
          (𝓝[>] 0) (𝓝 (lrCoord i q ω - sInf ((fun s => lrCoord i s ω) '' Icc t (q : ℝ)))))
    (hNC : ∀ᵐ ω ∂μ, LatticeProb.CorrelatedBM.NoCommonWeakContourPair ω)
    (hZ3 : ∀ᵐ ω ∂μ, (matingTriplePoints ω).Countable ∨
      ∃ d : ℝ≥0∞, dimH (matingTriplePoints ω) ≤ d ∧ d < 1 / 2) :
    μ (LatticeProb.CorrelatedBM.rigiditySet matingTriplePoints)ᶜ = 0 :=
  LatticeProb.CorrelatedBM.measure_compl_rigiditySet_eq_zero
    (LatticeProb.CorrelatedBM.ae_isRegularCoordinatePair hμ hγ0 hγ2 hdesc hexc) hNC hZ3

/-- **The rigidity pair from the four almost sure properties.** If every `γ`-correlated two-sided Brownian law,
`0 < γ < 2`, has the properties `hdesc`, `hexc`, `hNC`, `hZ3` of
`measure_compl_rigiditySet_matingTriplePoints_eq_zero`, then some one-sided mating-rigid set of pairs is full for
all these laws. -/
theorem exists_matingRigidLEOn_full
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
    : ∃ G : Set Path2, (∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ → μ Gᶜ = 0) ∧
      MatingRigidLEOn G :=
  ⟨_, fun γ hγ0 hγ2 μ hμ => measure_compl_rigiditySet_matingTriplePoints_eq_zero hμ hγ0 hγ2
    (hdesc γ hγ0 hγ2 μ hμ) (hexc γ hγ0 hγ2 μ hμ) (hNC γ hγ0 hγ2 μ hμ) (hZ3 γ hγ0 hγ2 μ hμ),
    matingRigidLEOn_rigiditySet⟩

section CountedRigidityInputs

/-- **Theorem 1.4** in the counted form `closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidity`, with the
rigidity pair `(hGnull, hG)` derived from the four almost sure properties `hdesc`, `hexc`, `hNC`, `hZ3` of every
`γ`-correlated two-sided Brownian law (`G` is the rigidity set of the triple points of the mating relation). Same
conclusion. -/
theorem closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hlow : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → S.mεCdf ε (c₁ * ε⁻¹) < 1 / 2)
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
  closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidity ν h1 h2 hlow h10 h11
    (G := LatticeProb.CorrelatedBM.rigiditySet matingTriplePoints)
    (fun γ hγ0 hγ2 μ hμ => measure_compl_rigiditySet_matingTriplePoints_eq_zero hμ hγ0 hγ2
      (hdesc γ hγ0 hγ2 μ hμ) (hexc γ hγ0 hγ2 μ hμ) (hNC γ hγ0 hγ2 μ hμ) (hZ3 γ hγ0 hγ2 μ hμ))
    matingRigidLEOn_rigiditySet hGFF hscale

/-- **Theorem 1.6** in the counted form `closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidity`, with the
rigidity pair `(hGnull, hG)` derived from the four almost sure properties `hdesc`, `hexc`, `hNC`, `hZ3` of every
`γ`-correlated two-sided Brownian law (`G` is the rigidity set of the triple points of the mating relation). Same
conclusion. -/
theorem closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hlow : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → S.mεCdf ε (c₁ * ε⁻¹) < 1 / 2)
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
  closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidity ν h1 h2 hlow h10 h11
    (G := LatticeProb.CorrelatedBM.rigiditySet matingTriplePoints)
    (fun γ hγ0 hγ2 μ hμ => measure_compl_rigiditySet_matingTriplePoints_eq_zero hμ hγ0 hγ2
      (hdesc γ hγ0 hγ2 μ hμ) (hexc γ hγ0 hγ2 μ hμ) (hNC γ hγ0 hγ2 μ hμ) (hZ3 γ hγ0 hγ2 μ hμ))
    matingRigidLEOn_rigiditySet hGFF hscale

end CountedRigidityInputs

end MatedCRT
