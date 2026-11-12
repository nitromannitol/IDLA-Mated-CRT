import MatedCRT.FirstPass.Derived.CoreExitTimeFromBG20
import MatedCRT.FirstPass.Derived.BG20Prop51OfBlocks

/-!
# Lemma 2.18 and the certified reference model core from the block degree estimate

BG20 Proposition 5.1 follows from the Green kernel upper bound (Lemma 5.4), the crude Green function bound
(Lemma 5.6), the volume growth, the cell size estimate (Lemma 2.8) and the block degree estimate (A.43)
(`bG20Prop51_of_blockDegree`). Hence Lemma 2.18 (`ExitTimeUpperBoundStmt`) follows from the same inputs, and
the conjuncts 14 and 16 of `CertifiedReferenceModelCore` (`FirstPass/S5qe.lean:33`) can be replaced by the
crude Green function bound and the block degree estimate: the Green kernel upper bound and the cell size
estimate are the conjuncts 12 and 5, and the volume growth is a theorem (`volumeGrowthStmt_holds`).

## Main results

* `exitTimeUpperBoundStmt_of_blockDegree`: Lemma 2.18 from Lemmas 5.4, 5.6, 2.8 and (A.43).
* `CertifiedReferenceModelCore.of_blockDegree`: the certified reference model core from its conjuncts other
  than 14 and 16, the crude Green function bound and the block degree estimate.
-/

open Set Metric MeasureTheory Filter Topology HarmonicBalls

namespace MatedCRT.FirstPass.Derived

/-- **Lemma 2.18 from the block degree estimate.** The exit time upper bound (Lemma 2.18) follows from the
Green kernel upper bound (Lemma 5.4), the crude Green function bound (Lemma 5.6), the cell size estimate
(Lemma 2.8) and the block degree estimate (A.43), through BG20 Proposition 5.1. -/
theorem exitTimeUpperBoundStmt_of_blockDegree {𝒮 : MatedCRT.SpaceFillingSLEModel}
    (h214 : MatedCRT.GreenKernelUpperBoundStmt 𝒮) (h215 : MatedCRT.GreenFunctionCrudeBoundStmt 𝒮)
    (hcell : MatedCRT.CellSizeEstimateStmt 𝒮)
    (hblock : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ κ : ℝ, 0 < κ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRT.MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ j : ℤ,
        (cell (⌊ε ^ (-(1 / 2 : ℝ))⌋₊ * ε) (S.η ω) j ∩ ball 0 ρ).Nonempty →
        |(∑ k ∈ Finset.Ioc ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * (j - 1)) ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * j),
            (matedDeg (S.mult ε ω) k : ℝ)) - 6 * ⌊ε ^ (-(1 / 2 : ℝ))⌋₊| ≤ ε ^ (-(1 / 2 : ℝ) + κ)}) :
    MatedCRT.ExitTimeUpperBoundStmt 𝒮 :=
  exitTimeUpperBoundStmt_of_bg20Prop51
    (MatedCRT.bG20Prop51_of_blockDegree h214 h215 volumeGrowthStmt_holds hcell hblock)

/-- **The certified reference model core from the block degree estimate.** The conjuncts of
`CertifiedReferenceModelCore` (`FirstPass/S5qe.lean:33`) other than 14 (Lemma 2.18) and 16 (BG20 Proposition
5.1), in the same order, together with the crude Green function bound (Lemma 5.6) and the block degree
estimate (A.43), give the core: conjunct 16 is `bG20Prop51_of_blockDegree` applied to the conjuncts 12 and 5,
and conjunct 14 follows from it. -/
theorem CertifiedReferenceModelCore.of_blockDegree {ν : ℝ → Measure MatedCRT.SLEPathCode}
    {𝒮 : MatedCRT.SpaceFillingSLEModel}
    (h1 : MatedCRT.HasNormalizedSLELaw 𝒮 ν) (h2 : MatedCRT.SLEModelClosureInput 𝒮)
    (h3 : MatedCRT.MepsScalingInput 𝒮) (h4 : MatedCRT.DegreeBoundInput 𝒮)
    (h5 : MatedCRT.CellSizeEstimateStmt 𝒮) (h6 : MatedCRT.CountingMeasureConvergenceStmt 𝒮)
    (h7 : MatedCRT.DegreeMeasureConvergenceStmt 𝒮) (h8 : MatedCRT.FrozenConeScalingLaw 𝒮)
    (h9 : MatedCRT.FrozenLBMGreenOccupationRescaled 𝒮) (h10 : MatedCRT.HasReferenceEnvironments 𝒮)
    (h11 : MatedCRT.RandomWalkToLBMStmt 𝒮) (h12 : MatedCRT.GreenKernelUpperBoundStmt 𝒮)
    (h13 : MatedCRT.GreenKernelLowerBoundStmt 𝒮)
    (h15 : MatedCRT.FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h17 : MatedCRT.FPSimilarityTransferCorrected 𝒮)
    (h215 : MatedCRT.GreenFunctionCrudeBoundStmt 𝒮)
    (hblock : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ κ : ℝ, 0 < κ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRT.MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ j : ℤ,
        (cell (⌊ε ^ (-(1 / 2 : ℝ))⌋₊ * ε) (S.η ω) j ∩ ball 0 ρ).Nonempty →
        |(∑ k ∈ Finset.Ioc ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * (j - 1)) ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * j),
            (matedDeg (S.mult ε ω) k : ℝ)) - 6 * ⌊ε ^ (-(1 / 2 : ℝ))⌋₊| ≤ ε ^ (-(1 / 2 : ℝ) + κ)}) :
    MatedCRT.CertifiedReferenceModelCore ν 𝒮 :=
  CertifiedReferenceModelCore.of_bg20Prop51 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h15
    (MatedCRT.bG20Prop51_of_blockDegree h12 h215 volumeGrowthStmt_holds h5 hblock) h17

end MatedCRT.FirstPass.Derived
