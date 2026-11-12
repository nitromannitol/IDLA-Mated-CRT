import MatedCRT.FirstPass.Derived.BlockBrownianRescale
import MatedCRT.FirstPass.Derived.CoreOfRunningMinTailLaw
import LatticeProb.Prob.BrownianRunningMinCount

/-!
# The running-minimum tail of a block of cells (Berestycki-Gwynne, Lemma A.9)

Let `X_i` be a coordinate of a correlated two-dimensional Brownian motion and consider a block
`[a + 1, a + N]` of `N` cells of mesh `ε`. A cell `a + j` of the block contains a running minimum of
`X_i` relative to the time `ε a` exactly when the unit interval `[j - 1, j]` contains a running-minimum
time of the Brownian motion `u ↦ ε^{-1/2} (X_i(ε a + ε u) - X_i(ε a))`
(`card_blockRunningMinCells_eq_card_forwardHits`); for the time reversal on the block, of the Brownian
motion `u ↦ ε^{-1/2} (X_i(ε (a + N) - ε u) - X_i(ε (a + N)))`. The number of such unit intervals among
the first `N` has the exponential tail `C exp(-c m / √N)` with absolute constants
(`LatticeProb.exists_measure_lt_card_runningMinHits_le`). This is Lemma A.9 of Berestycki-Gwynne
(arXiv:2003.10320), the hypothesis `hF6` of the block degree estimate.

## Main results

* `MatedCRT.exists_runningMinTail`: the tail bound, with constants independent of `γ`, of the
  correlated Brownian motion, of the coordinate, of the mesh and of the block.
* `MatedCRT.runningMinTail_holds`: the same in the form of the hypothesis `hF6`.
* `MatedCRT.FirstPass.Derived.hblock_of_degreeBound`: the block degree estimate (BG20 (A.43)) from
  the degree bound alone.
* `MatedCRT.FirstPass.Derived.degreeMeasureConvergenceStmt_of_envScaling`: Lemma 2.10 from the degree
  bound and the scaling of the environment.
* `CertifiedReferenceModelCore.of_runningMinTail_derived`, `_law_derived`, `_gff_derived`: the cores
  of `CoreOfRunningMinTail` and `CoreOfRunningMinTailLaw` without the hypothesis `hF6`.
-/

open MeasureTheory ProbabilityTheory Set Metric Finset MatedCRTHarmonic.MatedCRT
open MatedCRT.KilledOccupation HarmonicBalls MarkovProcess
open scoped NNReal

namespace MatedCRT

/-- **Running-minimum cells of a block (Berestycki-Gwynne, Lemma A.9).** There are constants `C` and
`c > 0` such that, for every correlated two-dimensional Brownian motion, either coordinate, every mesh
`ε > 0` and every block `[a + 1, a + N]` of `N ≥ 1` cells, the number of cells of the block containing a
running minimum of the coordinate, or of its time reversal on the block, exceeds `m` with probability
at most `C exp(-c m / √N)`. -/
theorem exists_runningMinTail : ∃ C c : ℝ, 0 < c ∧ ∀ (γ : ℝ) (μ : Measure Path2),
    IsCorrelatedBM2 γ μ → ∀ (i : Fin 2) (ε : ℝ), 0 < ε → ∀ (a : ℤ) (N : ℕ), 1 ≤ N → ∀ m : ℝ,
      μ {p | m < (#(blockRunningMinCells ε (fun t => lrCoord i t p) (a + 1) (a + N)) : ℝ)} ≤
          ENNReal.ofReal (C * Real.exp (-(c * m / Real.sqrt N))) ∧
        μ {p | m < (#(blockRunningMinCells ε
          (blockReversal ε (fun t => lrCoord i t p) (a + 1) (a + N)) (a + 1) (a + N)) : ℝ)} ≤
          ENNReal.ofReal (C * Real.exp (-(c * m / Real.sqrt N))) := by
  obtain ⟨C, c, hc, hBM⟩ := LatticeProb.exists_measure_lt_card_runningMinHits_le.{0}
  refine ⟨C, c, hc, fun γ μ hμ i ε hε a N hN m => ?_⟩
  lift ε to ℝ≥0 using hε.le
  have hε0 : 0 < ε := NNReal.coe_pos.1 hε
  have hfwd : ∀ p : Path2,
      #(blockRunningMinCells (ε : ℝ) (fun t => lrCoord i t p) (a + 1) (a + N)) =
        (LatticeProb.runningMinHits (blockForwardPath i ε ((ε : ℝ) * a)) N p).card := fun p =>
    (card_blockRunningMinCells_eq_card_forwardHits i hε0 a N p).trans rfl
  have hbwd : ∀ p : Path2,
      #(blockRunningMinCells (ε : ℝ) (blockReversal (ε : ℝ) (fun t => lrCoord i t p) (a + 1) (a + N))
        (a + 1) (a + N)) =
        (LatticeProb.runningMinHits (blockBackwardPath i ε ((ε : ℝ) * ((a + N : ℤ) : ℝ))) N p).card :=
    fun p => (card_blockRunningMinCells_blockReversal_eq_card_backwardHits i hε0 a N p).trans rfl
  simp only [hfwd, hbwd]
  exact ⟨hBM μ _ (isBrownianReal_blockForwardPath hμ i hε0.ne' _)
      (measurable_blockForwardPath i ε _) (continuous_blockForwardPath i ε _) N hN m,
    hBM μ _ (isBrownianReal_blockBackwardPath hμ i hε0.ne' _)
      (measurable_blockBackwardPath i ε _) (continuous_blockBackwardPath i ε _) N hN m⟩

/-- **The running-minimum tail `hF6`** (Berestycki-Gwynne, Lemma A.9), in the form taken by the block
degree estimate: for every `γ ∈ (0, 2)` there are constants `C` and `c > 0` such that the bound holds
for every correlated two-dimensional Brownian motion with parameter `γ`. -/
theorem runningMinTail_holds : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ C c : ℝ, 0 < c ∧
    ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ →
      ∀ (i : Fin 2) (ε : ℝ), 0 < ε → ∀ (a : ℤ) (N : ℕ), 1 ≤ N → ∀ m : ℝ,
        μ {p | m < (#(blockRunningMinCells ε (fun t => lrCoord i t p) (a + 1) (a + N)) : ℝ)} ≤
          ENNReal.ofReal (C * Real.exp (-(c * m / Real.sqrt N))) ∧
        μ {p | m < (#(blockRunningMinCells ε
          (blockReversal ε (fun t => lrCoord i t p) (a + 1) (a + N)) (a + 1) (a + N)) : ℝ)} ≤
          ENNReal.ofReal (C * Real.exp (-(c * m / Real.sqrt N))) := by
  intro γ _ _
  obtain ⟨C, c, hc, h⟩ := exists_runningMinTail
  exact ⟨C, c, hc, h γ⟩

end MatedCRT

namespace MatedCRT.FirstPass.Derived

/-- **The block degree estimate (Berestycki-Gwynne (A.43)) from the degree bound.** With
`N = ⌊ε^{-1/2}⌋`, with polynomially high probability every block of `N` cells meeting `B_ρ(0)` has total
degree within `ε^{-1/2 + κ}` of `6N`. The cell size estimate is `cellSizeEstimateStmt_holds`, the
distinctness of the cell minima is `bmCellMin_injective_ae` and the running-minimum tail is
`runningMinTail_holds`. -/
theorem hblock_of_degreeBound {𝒮 : SpaceFillingSLEModel} (hdeg : DegreeBoundInput 𝒮) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ κ : ℝ, 0 < κ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ j : ℤ,
        (cell (⌊ε ^ (-(1 / 2 : ℝ))⌋₊ * ε) (S.η ω) j ∩ ball 0 ρ).Nonempty →
        |(∑ k ∈ Finset.Ioc ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * (j - 1)) ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * j),
            (matedDeg (S.mult ε ω) k : ℝ)) - 6 * ⌊ε ^ (-(1 / 2 : ℝ))⌋₊| ≤
          ε ^ (-(1 / 2 : ℝ) + κ)} :=
  MatedCRT.hblock_of_runningMinTail (cellSizeEstimateStmt_holds 𝒮) hdeg
    (fun γ _ _ => MatedCRT.bmCellMin_injective_ae (γ := γ)) MatedCRT.runningMinTail_holds

/-- **Lemma 2.10 from the degree bound and the scaling of the environment.** The degree-weighted counting
measure converges: the cell size estimate, the quantum cone scaling and the running-minimum tail are
proved (`cellSizeEstimateStmt_holds`, `quantumConeScalingInput_derived`, `runningMinTail_holds`). -/
theorem degreeMeasureConvergenceStmt_of_envScaling {𝒮 : SpaceFillingSLEModel}
    (hEnv : ConeEnvironmentScalingStep 𝒮) (hdeg : DegreeBoundInput 𝒮) :
    DegreeMeasureConvergenceStmt 𝒮 :=
  MatedCRT.degreeMeasureConvergenceStmt_of_runningMinTail (cellSizeEstimateStmt_holds 𝒮)
    quantumConeScalingInput_derived hEnv hdeg MatedCRT.runningMinTail_holds

/-- `CertifiedReferenceModelCore.of_runningMinTail` with the running-minimum tail supplied by
`runningMinTail_holds`. -/
theorem CertifiedReferenceModelCore.of_runningMinTail_derived {ν : ℝ → Measure MatedCRT.SLEPathCode}
    {𝒮 : MatedCRT.SpaceFillingSLEModel}
    (h1 : MatedCRT.HasNormalizedSLELaw 𝒮 ν) (h2 : MatedCRT.SLEModelClosureInput 𝒮)
    (h3 : MatedCRT.MepsScalingInput 𝒮) (h4 : MatedCRT.DegreeBoundInput 𝒮)
    (h9 : MatedCRT.FrozenLBMGreenOccupationRescaled 𝒮) (h10 : MatedCRT.HasReferenceEnvironments 𝒮)
    (h11 : MatedCRT.RandomWalkToLBMStmt 𝒮) (h12 : MatedCRT.GreenKernelUpperBoundStmt 𝒮)
    (h13 : MatedCRT.GreenKernelLowerBoundStmt 𝒮)
    (h15 : MatedCRT.FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h17 : MatedCRT.FPSimilarityTransferCorrected 𝒮)
    (h215 : MatedCRT.GreenFunctionCrudeBoundStmt 𝒮)
    (hEnv : MatedCRT.ConeEnvironmentScalingStep 𝒮) :
    MatedCRT.CertifiedReferenceModelCore ν 𝒮 :=
  CertifiedReferenceModelCore.of_runningMinTail h1 h2 h3 h4 h9 h10 h11 h12 h13 h15 h17 h215 hEnv
    MatedCRT.runningMinTail_holds

/-- `CertifiedReferenceModelCore.of_runningMinTail_law` with the running-minimum tail supplied by
`runningMinTail_holds`. -/
theorem CertifiedReferenceModelCore.of_runningMinTail_law_derived
    {ν : ℝ → Measure MatedCRT.SLEPathCode} {𝒮 : MatedCRT.SpaceFillingSLEModel}
    (h1 : MatedCRT.HasNormalizedSLELaw 𝒮 ν) (h2 : MatedCRT.SLEModelClosureInput 𝒮)
    (h3 : MatedCRT.MepsScalingInput 𝒮) (h4 : MatedCRT.DegreeBoundInput 𝒮)
    (h9 : MatedCRT.FrozenLBMGreenOccupationRescaled 𝒮) (h10 : MatedCRT.HasReferenceEnvironments 𝒮)
    (h11 : MatedCRT.RandomWalkToLBMStmt 𝒮) (h12 : MatedCRT.GreenKernelUpperBoundStmt 𝒮)
    (h13 : MatedCRT.GreenKernelLowerBoundStmt 𝒮)
    (h15 : MatedCRT.FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h215 : MatedCRT.GreenFunctionCrudeBoundStmt 𝒮)
    (hEnv : MatedCRT.ConeEnvironmentScalingStep 𝒮) :
    MatedCRT.CertifiedReferenceModelCore ν 𝒮 :=
  CertifiedReferenceModelCore.of_runningMinTail_law h1 h2 h3 h4 h9 h10 h11 h12 h13 h15 h215 hEnv
    MatedCRT.runningMinTail_holds

/-- `CertifiedReferenceModelCore.of_runningMinTail_gff` with the running-minimum tail supplied by
`runningMinTail_holds`. -/
theorem CertifiedReferenceModelCore.of_runningMinTail_gff_derived
    {ν : ℝ → Measure MatedCRT.SLEPathCode} {𝒮 : MatedCRT.SpaceFillingSLEModel}
    (h1 : MatedCRT.HasNormalizedSLELaw 𝒮 ν) (h2 : MatedCRT.SLEModelClosureInput 𝒮)
    (h3 : MatedCRT.MepsScalingInput 𝒮) (h4 : MatedCRT.DegreeBoundInput 𝒮)
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
  CertifiedReferenceModelCore.of_runningMinTail_gff h1 h2 h3 h4 h10 h11 h12 h13 h15 h215 hEnv
    MatedCRT.runningMinTail_holds hGFF

end MatedCRT.FirstPass.Derived
