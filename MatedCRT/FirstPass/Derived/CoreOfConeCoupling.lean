import MatedCRT.FirstPass.Derived.CellSizeOfConeCoupling
import MatedCRT.FirstPass.Derived.CoreExitTimeOfBlocks

/-!
# The certified reference model core from the coupling of the quantum cone with a whole-plane GFF

The conjunct 5 of `CertifiedReferenceModelCore` (`FirstPass/S5qe.lean:33`) is the cell size estimate
(Lemma 2.8, BG20 Lemma 2.4). It holds for every space-filling SLE model given the coupling
`ConeWholePlaneCouplingStep` of the `γ`-quantum cone on `B_1` with a whole-plane GFF minus `γ log |·|`
(`cellSizeEstimateStmt_of_coneCoupling`). Combined with `CertifiedReferenceModelCore.of_blockDegree`, the core
follows from its conjuncts other than 5, 14 and 16, the coupling step, the crude Green function bound (Lemma 5.6)
and the block degree estimate (BG20 (A.43)).

## Main results

* `CertifiedReferenceModelCore.of_coneCoupling_blockDegree`: the certified reference model core without the cell
  size estimate among its hypotheses.
-/

open Set Metric MeasureTheory Filter Topology HarmonicBalls

namespace MatedCRT.FirstPass.Derived

/-- **The certified reference model core from the cone coupling and the block degree estimate.** The conjuncts of
`CertifiedReferenceModelCore` (`FirstPass/S5qe.lean:33`) other than 5 (Lemma 2.8), 14 (Lemma 2.18) and 16 (BG20
Proposition 5.1), in the same order, together with the coupling of the quantum cone with a whole-plane GFF on `B_1`
(`ConeWholePlaneCouplingStep`, which gives conjunct 5), the crude Green function bound (Lemma 5.6) and the block degree
estimate (A.43), give the core. -/
theorem CertifiedReferenceModelCore.of_coneCoupling_blockDegree {ν : ℝ → Measure MatedCRT.SLEPathCode}
    {𝒮 : MatedCRT.SpaceFillingSLEModel}
    (h1 : MatedCRT.HasNormalizedSLELaw 𝒮 ν) (h2 : MatedCRT.SLEModelClosureInput 𝒮)
    (h3 : MatedCRT.MepsScalingInput 𝒮) (h4 : MatedCRT.DegreeBoundInput 𝒮)
    (hcpl : MatedCRT.ConeWholePlaneCouplingStep) (h6 : MatedCRT.CountingMeasureConvergenceStmt 𝒮)
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
  CertifiedReferenceModelCore.of_blockDegree h1 h2 h3 h4 (cellSizeEstimateStmt_of_coneCoupling hcpl 𝒮) h6 h7
    h8 h9 h10 h11 h12 h13 h15 h17 h215 hblock

end MatedCRT.FirstPass.Derived
