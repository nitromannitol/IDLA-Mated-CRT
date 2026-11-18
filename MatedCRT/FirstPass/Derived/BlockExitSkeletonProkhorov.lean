import MatedCRT.FirstPass.Derived.BlockExitSkeletonAssembly
import LatticeProb.Prob.KernelProkhorovChain

/-!
# The stopped-path comparison from a one-sided Prokhorov bound for the block-exit skeletons

`MatedCRT.BlockExit.measure_stopAtExit_le_of_transfer` compares the laws of the walk and of the Brownian
motion stopped at their exit times from `U`, given the transfer bound `hTrans` for the sets of stopped paths
`stopPreimage U A₀`.  The transfer bound is the measure-theoretic transfer of a one-sided Prokhorov bound
`ProkhorovLE` between the laws of the block-exit position histories (the skeletons) to the laws of the stopped
curves: the reconstruction `stepPath N` is `1`-Lipschitz from the sup distance of histories to the distance
`cmpEDist` of curves modulo time parametrization, and on the events `G₁`, `G₂` (the path reaches `farSet U d'`
within `N` blocks, and for the Brownian motion also `GoodStop U T η d ε`) the stopped path is within `a`, `a'`
`> 8 s` of the reconstruction of its skeleton.

* `MatedCRT.BlockExit.measure_stopAtExit_le_of_prokhorovLE_of_transferLemma`: the composition, with the
  general transfer lemma (`LatticeProb.measure_preimage_le_of_prokhorovLE_of_approx`, specialized to the
  skeleton space `Fin (N + 1) → ℂ` and the curve space `ℝ≥0 → ℂ` with `cmpEDist`) as the explicit hypothesis
  `hLP`.  All other hypotheses of the transfer lemma (triangle inequality of `cmpEDist`, `1`-Lipschitz
  reconstruction, measurability of the skeleton maps, the two approximation events) are proved here.
-/

set_option autoImplicit false

open MeasureTheory Set Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

open LatticeProb MatedCRT.StopAtExitCmp

/-- **Stopped-path comparison from a one-sided Prokhorov bound for the block-exit skeletons**, with the general
transfer lemma as the explicit hypothesis `hLP`. -/
theorem measure_stopAtExit_le_of_prokhorovLE_of_transferLemma {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] (μ : Measure Ω₁) (ν : Measure Ω₂) (W : Ω₁ → ContinuousPath ℂ)
    (B : Ω₂ → ContinuousPath ℂ) (hW : Measurable W) (hB : Measurable B) {s : ℝ} (hs : 0 < s)
    {U : Set ℂ} {T η : ℝ≥0} {d d' ε κ δ e a a' : ℝ} (hη : 0 < η) (hd' : 0 < d') (hdd : 4 * s + d' ≤ d)
    {N : ℕ} (hεκ : 2 * ε < κ) (hκ : 0 < κ) (hr : a' + δ + a ≤ min ε d') (ha : 8 * s < a)
    (ha' : 8 * s < a') (hδ : 0 ≤ δ)
    (hP : ProkhorovLE (μ.map fun ω => blockExitPositions s (farSet U d') N (W ω))
      (ν.map fun ω => blockExitPositions s (farSet U d') N (B ω)) δ e)
    (hLP : (∀ x y z : ℝ≥0 → ℂ, cmpEDist x z ≤ cmpEDist x y + cmpEDist y z) →
      (∀ x x' : Fin (N + 1) → ℂ, cmpEDist (stepPath N x) (stepPath N x') ≤ edist x x') →
      ∀ {H₁ : Ω₁ → Fin (N + 1) → ℂ} {H₂ : Ω₂ → Fin (N + 1) → ℂ}, Measurable H₁ → Measurable H₂ →
      ∀ {δ e a a' : ℝ}, 0 ≤ a → 0 ≤ a' → 0 ≤ δ → ProkhorovLE (μ.map H₁) (ν.map H₂) δ e →
      ∀ {P₁ : Ω₁ → ℝ≥0 → ℂ} {P₂ : Ω₂ → ℝ≥0 → ℂ} {G₁ : Set Ω₁} {G₂ : Set Ω₂},
      (∀ ω ∈ G₁, cmpEDist (stepPath N (H₁ ω)) (P₁ ω) < ENNReal.ofReal a) →
      (∀ ω ∈ G₂, cmpEDist (P₂ ω) (stepPath N (H₂ ω)) < ENNReal.ofReal a') →
      ∀ A : Set (ℝ≥0 → ℂ), μ (P₁ ⁻¹' A) ≤
        ν {ω | ∃ f ∈ A, cmpEDist (P₂ ω) f < ENNReal.ofReal (a' + δ + a)} + ENNReal.ofReal e +
          μ G₁ᶜ + ν G₂ᶜ)
    (A₀ : Set (ℝ≥0 → ℂ)) :
    μ {ω | stopAtExit U (W ω) ∈ A₀} ≤
      ν {ω | ∃ f' ∈ A₀, cmpEDist (stopAtExit U (B ω)) f' < ENNReal.ofReal κ} +
        ENNReal.ofReal e +
        2 * μ {ω | ∃ n ≤ N, W ω (blockExitTimes s (farSet U d') n (W ω)) ∈ farSet U d'}ᶜ +
        2 * ν {ω | (∃ n ≤ N, B ω (blockExitTimes s (farSet U d') n (B ω)) ∈ farSet U d') ∧
          GoodStop U T η d ε (B ω)}ᶜ := by
  have hF : MeasurableSet (farSet U d') := (isClosed_farSet U d').measurableSet
  have ha0 : 0 ≤ a := by linarith
  have ha0' : 0 ≤ a' := by linarith
  refine measure_stopAtExit_le_of_transfer μ ν W B hs hη hd' hdd hεκ hκ hr A₀ ?_
  exact hLP cmpEDist_triangle (cmpEDist_stepPath_le N)
    ((measurable_blockExitPositions s hF N).comp hW) ((measurable_blockExitPositions s hF N).comp hB)
    ha0 ha0' hδ hP
    (fun ω hω => cmpEDist_stepPath_blockStopped_lt hs hω ha)
    (fun ω hω => cmpEDist_blockStopped_stepPath_lt hs hω.1 ha') _

end BlockExit

end MatedCRT
