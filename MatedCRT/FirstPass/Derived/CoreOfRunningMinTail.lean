import MatedCRT.FirstPass.Derived.CellSizeOfConeCouplingProd
import MatedCRT.FirstPass.Derived.CountingMeasureOfCellSize
import MatedCRT.FirstPass.Derived.DegreeMeasureOfRunningMinTail
import MatedCRT.FirstPass.Derived.ConeScalingLawDerived

/-!
# The core of the reference model from the running-minimum tail of a correlated Brownian motion

`CertifiedReferenceModelCore.of_blockDegree_cellSize` builds the core of the certified reference model from its
conjuncts other than the cell size estimate (Lemma 2.8, now `cellSizeEstimateStmt_holds`) and the conjuncts derived
inside it, together with the block degree estimate `hblock`. Four more of its hypotheses are now theorems or follow
from smaller inputs:

* conjunct 6, the convergence of the counting measure (Lemma 2.9, Berestycki-Gwynne arXiv:2003.10320 Lemma A.4), is
  `countingMeasureConvergenceStmt_of_cellSize` applied to Lemma 2.8;
* conjunct 7, the convergence of the degree measure (Lemma 2.10, Berestycki-Gwynne Corollary A.6), is
  `degreeMeasureConvergenceStmt_of_runningMinTail`, from Lemma 2.8, the scale invariance of the quantum cone
  (`quantumConeScalingInput_derived`), the scaling of the environment `ConeEnvironmentScalingStep 𝒮`, the degree bound
  (conjunct 4) and the tail `hF6` of the number of running-minimum cells of a block of a correlated two-dimensional
  Brownian motion (Berestycki-Gwynne Lemma A.9);
* the block degree estimate `hblock` is `hblock_of_runningMinTail` from the same inputs (the almost sure injectivity of
  the cell minima is `bmCellMin_injective_ae`);
* conjunct 8, the scaling in law of the quantum cone (Duplantier-Miller-Sheffield arXiv:1409.7055 Proposition 4.13(i)),
  is `frozenConeScalingLaw_derived`.

`CertifiedReferenceModelCore.of_runningMinTail` takes the remaining conjuncts together with `ConeEnvironmentScalingStep 𝒮`
and `hF6`.
-/

open MeasureTheory Set Metric MatedCRTHarmonic.MatedCRT
open scoped Finset

namespace MatedCRT.FirstPass.Derived

/-- **The core of the certified reference model from the running-minimum tail.** The conjuncts 5 (Lemma 2.8),
6 (Lemma 2.9), 7 (Lemma 2.10) and 8 (cone scaling in law) of `CertifiedReferenceModelCore` and the block degree estimate
are supplied: the hypotheses are the other conjuncts, the crude Green function bound, the scaling of the environment
and the tail `hF6` of the number of running-minimum cells (Berestycki-Gwynne arXiv:2003.10320 Lemma A.9). -/
theorem CertifiedReferenceModelCore.of_runningMinTail {ν : ℝ → Measure MatedCRT.SLEPathCode}
    {𝒮 : MatedCRT.SpaceFillingSLEModel}
    (h1 : MatedCRT.HasNormalizedSLELaw 𝒮 ν) (h2 : MatedCRT.SLEModelClosureInput 𝒮)
    (h3 : MatedCRT.MepsScalingInput 𝒮) (h4 : MatedCRT.DegreeBoundInput 𝒮)
    (h9 : MatedCRT.FrozenLBMGreenOccupationRescaled 𝒮) (h10 : MatedCRT.HasReferenceEnvironments 𝒮)
    (h11 : MatedCRT.RandomWalkToLBMStmt 𝒮) (h12 : MatedCRT.GreenKernelUpperBoundStmt 𝒮)
    (h13 : MatedCRT.GreenKernelLowerBoundStmt 𝒮)
    (h15 : MatedCRT.FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h17 : MatedCRT.FPSimilarityTransferCorrected 𝒮)
    (h215 : MatedCRT.GreenFunctionCrudeBoundStmt 𝒮)
    (hEnv : MatedCRT.ConeEnvironmentScalingStep 𝒮)
    (hF6 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ C c : ℝ, 0 < c ∧ ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ →
      ∀ (i : Fin 2) (ε : ℝ), 0 < ε → ∀ (a : ℤ) (N : ℕ), 1 ≤ N → ∀ m : ℝ,
        μ {p | m < (#(MatedCRT.blockRunningMinCells ε (fun t => lrCoord i t p) (a + 1) (a + N)) : ℝ)} ≤
          ENNReal.ofReal (C * Real.exp (-(c * m / Real.sqrt N))) ∧
        μ {p | m < (#(MatedCRT.blockRunningMinCells ε
          (MatedCRT.blockReversal ε (fun t => lrCoord i t p) (a + 1) (a + N)) (a + 1) (a + N)) : ℝ)} ≤
          ENNReal.ofReal (C * Real.exp (-(c * m / Real.sqrt N)))) :
    MatedCRT.CertifiedReferenceModelCore ν 𝒮 := by
  have h5 := cellSizeEstimateStmt_holds 𝒮
  exact CertifiedReferenceModelCore.of_blockDegree_cellSize h1 h2 h3 h4
    (MatedCRT.countingMeasureConvergenceStmt_of_cellSize h5)
    (MatedCRT.degreeMeasureConvergenceStmt_of_runningMinTail h5 quantumConeScalingInput_derived hEnv h4 hF6)
    (frozenConeScalingLaw_derived 𝒮) h9 h10 h11 h12 h13 h15 h17 h215
    (MatedCRT.hblock_of_runningMinTail h5 h4 (fun γ _ _ => MatedCRT.bmCellMin_injective_ae (γ := γ)) hF6)

end MatedCRT.FirstPass.Derived
