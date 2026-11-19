import MatedCRT.FirstPass.Derived.BrownianBlockExitReachGoodStop

/-!
# Planar Brownian motion reaches a sandwiched frozen set within `N` blocks and stops well

`BrownianBlockExitReachGoodStop` for a block chain frozen on a set `F` with `farSet U d₁ ⊆ F`
instead of `F = farSet U d'`: a chain that avoids `F` stays in the closed disc of radius `R + d₁`
(`U ⊆ ball 0 R`), and the frozen-hit bound applies with `d₁` in place of `d'`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric MarkovProcess
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

open MatedCRT.StopAtExitCmp

/-- The block chain of planar Brownian motion reaches every frozen set `F ⊇ farSet U d₁` within
`N` blocks, uniformly in the start `z ∈ closedBall 0 ρ`. -/
theorem planarBrownianMotion_not_reach_of_farSet_subset {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (p : ℕ) :
    ∃ C : ℝ, ∀ {R ρ d₁ : ℝ}, 0 < R → 0 ≤ ρ → 0 < d₁ → ∀ {U : Set ℂ}, U ⊆ ball (0 : ℂ) R →
      ∀ {F : Set ℂ}, farSet U d₁ ⊆ F →
      ∀ z ∈ closedBall (0 : ℂ) ρ, ∀ s : ℝ, 0 < s → ∀ r : ℝ, 0 < r → r < 1 →
        4 * ((R + d₁ + ρ + 4 * s + 1) * r) ≤ s → ∀ N : ℕ, ⌊r ^ (-(2 + ζ))⌋₊ ≤ N + 1 →
          planarBrownianMotion z
              {ω : ContinuousPath ℂ | ¬ ∃ n ≤ N, ω (blockExitTimes s F n ω) ∈ F} ≤
            ENNReal.ofReal (C * r ^ p) := by
  obtain ⟨C, hC⟩ := planarBrownianMotion_blockExit_avoid_frozen_superpoly hζ0 hζ1 p
  refine ⟨C, fun {R ρ d₁} hR hρ hd₁ {U} hU {F} hF z hz s hs r hr0 hr1 hars N hN => ?_⟩
  have hρz : ‖z‖ ≤ ρ := by simpa using hz
  have ha : 0 < R + d₁ + ρ + 4 * s + 1 := by linarith
  refine le_trans (measure_mono ?_)
    (hC z s hs F (closedBall (0 : ℂ) (R + d₁)) (R + d₁ + ρ + 4 * s + 1) r ha hr0 hr1
      hars (fun y hy => ?_))
  · intro ω hω n hn
    have hnN : n ≤ N := by omega
    have hnF : ω (blockExitTimes s F n ω) ∉ F := fun h => hω ⟨n, hnN, h⟩
    refine ⟨hnF, ?_⟩
    by_contra hK
    exact hnF (hF (mem_farSet_of_ball_subset hU (by
      have : R + d₁ < ‖ω (blockExitTimes s F n ω)‖ := by simpa using hK
      exact this.le)))
  · have hy' : ‖y‖ ≤ R + d₁ := by simpa using hy
    have : ‖y - z‖ ≤ ‖y‖ + ‖z‖ := norm_sub_le y z
    linarith

/-- **The Brownian side of the stopped-path comparison for a sandwiched frozen set, uniformly in
the start.** As `exists_planarBrownianMotion_reach_and_goodStop_compl_le`, for every `F` with
`farSet (ball 0 R) d₁ ⊆ F` and `d₁` in place of `d'`. -/
theorem exists_planarBrownianMotion_reach_and_goodStop_compl_le_sandwich {ρ R : ℝ} (hρ : 0 ≤ ρ)
    (hρR : ρ < R) {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (p : ℕ) :
    ∃ (T η : ℝ≥0) (d C : ℝ), 0 < η ∧ 0 < d ∧ ∀ {d₁ : ℝ}, 0 < d₁ → ∀ {F : Set ℂ},
      farSet (ball (0 : ℂ) R) d₁ ⊆ F →
      ∀ z ∈ closedBall (0 : ℂ) ρ, ∀ s : ℝ, 0 < s → ∀ r : ℝ, 0 < r → r < 1 →
        4 * ((R + d₁ + ρ + 4 * s + 1) * r) ≤ s → ∀ N : ℕ, ⌊r ^ (-(2 + ζ))⌋₊ ≤ N + 1 →
          planarBrownianMotion z
              {ω : ContinuousPath ℂ |
                (∃ n ≤ N, ω (blockExitTimes s F n ω) ∈ F) ∧
                  GoodStop (ball (0 : ℂ) R) T η d ε ω}ᶜ ≤
            ENNReal.ofReal (C * r ^ p) + ENNReal.ofReal θ := by
  obtain ⟨T, η, hη, d, hd, hU⟩ := exists_forall_planarBrownianMotion_not_goodStop_lt hρ hρR hε hθ
  obtain ⟨C, hC⟩ := planarBrownianMotion_not_reach_of_farSet_subset hζ0 hζ1 p
  have hR : 0 < R := lt_of_le_of_lt hρ hρR
  refine ⟨T, η, d, C, hη, hd, fun {d₁} hd₁ {F} hF z hz s hs r hr0 hr1 hars N hN => ?_⟩
  refine le_trans (measure_mono compl_reach_and_goodStop_subset) (le_trans (measure_union_le _ _) ?_)
  exact add_le_add (hC hR hρ hd₁ subset_rfl hF z hz s hs r hr0 hr1 hars N hN) (hU z hz).le

end BlockExit

end MatedCRT
