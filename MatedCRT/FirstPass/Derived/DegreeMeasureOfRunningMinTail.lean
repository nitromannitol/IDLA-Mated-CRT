import MatedCRT.FirstPass.Derived.BlockDegreeOfRunningMinTail
import MatedCRT.FirstPass.Derived.BlockCellMinInjective

/-!
# Lemma 2.10 from the running-minimum tail of Brownian motion

The degree-weighted measure convergence `DegreeMeasureConvergenceStmt` (BG20 Lemma A.5 route) follows from
the cell size estimate, the quantum cone scaling input, the environment scaling step and the block degree
estimate (A.43) (`degreeMeasureConvergenceStmt_of_blockDegree`). The block degree estimate follows from the
degree bound, almost sure distinctness of the cell minima of a correlated Brownian path and the tail of the
running-minimum count of a block (`hblock_of_runningMinTail`); distinctness of the cell minima is proved
(`bmCellMin_injective_ae`). What remains of the block degree estimate is the running-minimum tail `hF6`
(BG20 Lemma A.9, after Brownian scaling): the number of cells of a block of `N` cells containing a running
minimum of a coordinate, or of its time reversal on the block, exceeds `m` with probability at most
`C exp(-c m / √N)`.

## Main result
* `degreeMeasureConvergenceStmt_of_runningMinTail`.
-/

open Set Metric MeasureTheory MatedCRTHarmonic.MatedCRT
open scoped Finset

namespace MatedCRT

/-- **The degree-weighted measure convergence from the running-minimum tail.** Given the cell size
estimate, the quantum cone scaling input, the environment scaling step, the degree bound and the tail
`C exp(-c m / √N)` of the number of cells of a block of `N` cells containing a running minimum of a
coordinate of a correlated Brownian path or of its reversal on the block (BG20 Lemma A.9), the
degree-weighted counting measure converges: `DegreeMeasureConvergenceStmt 𝒮`. -/
theorem degreeMeasureConvergenceStmt_of_runningMinTail {𝒮 : SpaceFillingSLEModel}
    (hcell : CellSizeEstimateStmt 𝒮) (hscale : QuantumConeScalingInput)
    (hEnv : ConeEnvironmentScalingStep 𝒮) (hdeg : DegreeBoundInput 𝒮)
    (hF6 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ C c : ℝ, 0 < c ∧ ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ →
      ∀ (i : Fin 2) (ε : ℝ), 0 < ε → ∀ (a : ℤ) (N : ℕ), 1 ≤ N → ∀ m : ℝ,
        μ {p | m < (#(blockRunningMinCells ε (fun t => lrCoord i t p) (a + 1) (a + N)) : ℝ)} ≤
          ENNReal.ofReal (C * Real.exp (-(c * m / Real.sqrt N))) ∧
        μ {p | m < (#(blockRunningMinCells ε
          (blockReversal ε (fun t => lrCoord i t p) (a + 1) (a + N)) (a + 1) (a + N)) : ℝ)} ≤
          ENNReal.ofReal (C * Real.exp (-(c * m / Real.sqrt N)))) :
    DegreeMeasureConvergenceStmt 𝒮 :=
  degreeMeasureConvergenceStmt_of_blockDegree hcell hscale hEnv
    (hblock_of_runningMinTail hcell hdeg (fun γ _ _ => bmCellMin_injective_ae (γ := γ)) hF6)

end MatedCRT
