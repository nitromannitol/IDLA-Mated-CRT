import MatedCRT.FirstPass.Derived.BlockExitSkeletonJoinParametersSandwich
import LatticeProb.Prob.ProkhorovLEApproxTransfer

/-!
# Block parameters for a sandwiched frozen set, without the transfer hypothesis

`exists_blockExit_parameters_allSet_le_sandwich_derived` is
`exists_blockExit_parameters_allSet_le_sandwich` with the general transfer lemma of the skeleton
comparison supplied by `LatticeProb.measure_preimage_le_of_prokhorovLE_of_approx`. What remains
are the block-exit hypotheses on the process `W`: the one-sided Prokhorov bound of the block-exit
positions, frozen on `F`, against planar Brownian motion and the reach of `F` within `N` blocks.
-/

set_option autoImplicit false

open MeasureTheory Set Metric MarkovProcess
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

open LatticeProb MatedCRT.StopAtExitCmp

universe u

/-- **Choice of the block parameters for the stopped-path comparison, sandwiched frozen set, with the
transfer lemma proved.** The
parameters `s, d', d₁, δ₀, N` do not depend on the frozen set `F`, which ranges over the measurable
sets with `farSet (ball 0 R) d₁ ⊆ F ⊆ farSet (ball 0 R) d'`. -/
theorem exists_blockExit_parameters_allSet_le_sandwich_derived {ρ R : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (s d' d₁ δ₀ : ℝ) (N : ℕ), 0 < s ∧ 0 < d' ∧ d' + 2 * s ≤ d₁ ∧ 0 < δ₀ ∧
      ∀ {F : Set ℂ}, MeasurableSet F → farSet (ball (0 : ℂ) R) d₁ ⊆ F →
      F ⊆ farSet (ball (0 : ℂ) R) d' →
      (∀ z ∈ closedBall (0 : ℂ) ρ, planarBrownianMotion z
        {b : ContinuousPath ℂ | ∃ j ≤ N, b (blockExitTimes s F j b) ∈
          F}ᶜ ≤ ENNReal.ofReal (κ / 16)) ∧
      ∀ {Ω₁ : Type u} [MeasurableSpace Ω₁] (μ : Measure Ω₁) (W : Ω₁ → ContinuousPath ℂ), Measurable W →
        ∀ x₀ ∈ closedBall (0 : ℂ) ρ, ∀ {δ e : ℝ}, 0 ≤ δ → δ ≤ δ₀ → e ≤ κ / 4 →
        ProkhorovLE (μ.map fun ω => blockExitPositions s F N (W ω))
          ((planarBrownianMotion x₀).map
            fun b => blockExitPositions s F N b) δ e →
        μ {ω | ∃ n ≤ N, W ω (blockExitTimes s F n (W ω)) ∈
            F}ᶜ ≤ ENNReal.ofReal (κ / 8) →
        ∀ A : Set (ℝ≥0 → ℂ),
          μ {ω | stopAtExit (ball (0 : ℂ) R) (W ω) ∈ A} ≤
            planarBrownianMotion x₀
              {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal κ} +
              ENNReal.ofReal κ := by
  obtain ⟨s, d', d₁, δ₀, N, hs, hd', hd₁, hδ₀, H⟩ :=
    exists_blockExit_parameters_allSet_le_sandwich.{u} hρ hρR hκ
  refine ⟨s, d', d₁, δ₀, N, hs, hd', hd₁, hδ₀, ?_⟩
  intro F hFm hF₁ hF₂
  obtain ⟨hguard, H'⟩ := H hFm hF₁ hF₂
  refine ⟨hguard, ?_⟩
  intro Ω₁ _ μ W hW x₀ hx₀ δ e hδ0 hδ he hP hreach A
  refine H' μ W hW x₀ hx₀ hδ0 hδ he hP hreach ?_ A
  intro htri hlip H₁ H₂ hH₁ hH₂ δ' e' a a' ha ha' hδ' hP' P₁ P₂ G₁ G₂ hG₁ hG₂ A'
  exact measure_preimage_le_of_prokhorovLE_of_approx htri hlip hH₁ hH₂ ha ha' hδ' hP' hG₁ hG₂ A'

end BlockExit

end MatedCRT
