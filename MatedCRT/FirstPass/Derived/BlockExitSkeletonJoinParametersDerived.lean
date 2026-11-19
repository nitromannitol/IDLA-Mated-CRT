import MatedCRT.FirstPass.Derived.BlockExitSkeletonJoinParameters
import LatticeProb.Prob.ProkhorovLEApproxTransfer

/-!
# The stopped-path comparison from block-exit data, without the transfer hypothesis

`exists_blockExit_parameters_allSet_le_derived` is `exists_blockExit_parameters_allSet_le` with the general transfer
lemma of the skeleton comparison supplied by `LatticeProb.measure_preimage_le_of_prokhorovLE_of_approx` (the
reconstruction of a curve from its block-exit skeleton, `stepPath N`, is `1`-Lipschitz for the extended distance
`cmpEDist`, which satisfies the triangle inequality).  What remains are the block-exit hypotheses on the process
`W`: the one-sided Prokhorov bound of the block-exit positions against planar Brownian motion and the reach of the
far set within `N` blocks.
-/

set_option autoImplicit false

open MeasureTheory Set Metric MarkovProcess
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

open LatticeProb MatedCRT.StopAtExitCmp

universe u

/-- **Choice of the block parameters for the stopped-path comparison, with the transfer lemma proved.** -/
theorem exists_blockExit_parameters_allSet_le_derived {ρ R : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R) {κ : ℝ}
    (hκ : 0 < κ) :
    ∃ (s d' δ₀ : ℝ) (N : ℕ), 0 < s ∧ 0 < d' ∧ 0 < δ₀ ∧
      (∀ z ∈ closedBall (0 : ℂ) ρ, planarBrownianMotion z
        {b : ContinuousPath ℂ | ∃ j ≤ N, b (blockExitTimes s (farSet (ball (0 : ℂ) R) d') j b) ∈
          farSet (ball (0 : ℂ) R) d'}ᶜ ≤ ENNReal.ofReal (κ / 16)) ∧
      ∀ {Ω₁ : Type u} [MeasurableSpace Ω₁] (μ : Measure Ω₁) (W : Ω₁ → ContinuousPath ℂ), Measurable W →
        ∀ x₀ ∈ closedBall (0 : ℂ) ρ, ∀ {δ e : ℝ}, 0 ≤ δ → δ ≤ δ₀ → e ≤ κ / 4 →
        ProkhorovLE (μ.map fun ω => blockExitPositions s (farSet (ball (0 : ℂ) R) d') N (W ω))
          ((planarBrownianMotion x₀).map
            fun b => blockExitPositions s (farSet (ball (0 : ℂ) R) d') N b) δ e →
        μ {ω | ∃ n ≤ N, W ω (blockExitTimes s (farSet (ball (0 : ℂ) R) d') n (W ω)) ∈
            farSet (ball (0 : ℂ) R) d'}ᶜ ≤ ENNReal.ofReal (κ / 8) →
        ∀ A : Set (ℝ≥0 → ℂ),
          μ {ω | stopAtExit (ball (0 : ℂ) R) (W ω) ∈ A} ≤
            planarBrownianMotion x₀
              {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal κ} +
              ENNReal.ofReal κ := by
  obtain ⟨s, d', δ₀, N, hs, hd', hδ₀, hguard, H⟩ := exists_blockExit_parameters_allSet_le.{u} hρ hρR hκ
  refine ⟨s, d', δ₀, N, hs, hd', hδ₀, hguard, ?_⟩
  intro Ω₁ _ μ W hW x₀ hx₀ δ e hδ0 hδ he hP hreach A
  refine H μ W hW x₀ hx₀ hδ0 hδ he hP hreach ?_ A
  intro htri hlip H₁ H₂ hH₁ hH₂ δ' e' a a' ha ha' hδ' hP' P₁ P₂ G₁ G₂ hG₁ hG₂ A'
  exact measure_preimage_le_of_prokhorovLE_of_approx htri hlip hH₁ hH₂ ha ha' hδ' hP' hG₁ hG₂ A'

end BlockExit

end MatedCRT
