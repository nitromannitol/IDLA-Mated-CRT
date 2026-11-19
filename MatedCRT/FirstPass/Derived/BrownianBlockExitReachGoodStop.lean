import MatedCRT.FirstPass.Derived.BrownianBlockExitFrozenHit
import MatedCRT.FirstPass.Derived.BrownianGoodStopAssembly
import MatedCRT.FirstPass.Derived.BlockExitSkeletonGoodStop

/-!
# Planar Brownian motion reaches the far set within `N` blocks and stops well, uniformly in the start

The comparison of the walk and of planar Brownian motion stopped at their exit times from `U` charges
the Brownian side with the probability of the complement of the event
`G₂ = {the block chain reaches farSet U d' within N blocks} ∩ {GoodStop U T η d ε}`.
For `U ⊆ ball 0 R` and a start `z` in a disc `closedBall 0 ρ` with `ρ < R`, both parts are controlled
uniformly in `z`:

* `planarBrownianMotion_not_reach_farSet_le`: a point of norm at least `R + d'` lies in `farSet U d'`,
  so a block chain started in `closedBall 0 ρ` that avoids `farSet U d'` stays in the closed disc of
  radius `R + d'`, and the frozen-hit bound of `BrownianBlockExitFrozenHit` gives
  `P_z(no block exit n ≤ N lies in farSet U d') ≤ C r ^ p` as soon as `⌊r ^ (-(2 + ζ))⌋ ≤ N + 1` and
  `4 (R + d' + ρ + 4 s + 1) r ≤ s`.
* `exists_planarBrownianMotion_reach_and_goodStop_compl_le`: fixing `(T, η, d)` for `(ε, θ)` by
  `exists_forall_planarBrownianMotion_not_goodStop_lt`, the union bound gives
  `P_z(G₂ᶜ) ≤ C r ^ p + θ` for every `z ∈ closedBall 0 ρ`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric MarkovProcess
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

open MatedCRT.StopAtExitCmp

/-- Every point of norm at least `R + d'` lies in `farSet U d'` when `U ⊆ ball 0 R`. -/
theorem mem_farSet_of_ball_subset {R d' : ℝ} {U : Set ℂ} (hU : U ⊆ ball (0 : ℂ) R) {y : ℂ}
    (hy : R + d' ≤ ‖y‖) : y ∈ farSet U d' := by
  intro w hw hwU
  have h1 : ‖w‖ < R := mem_ball_zero_iff.1 (hU hwU)
  have h2 : ‖y‖ - ‖w‖ ≤ ‖y - w‖ := norm_sub_norm_le y w
  have h3 : ‖y - w‖ < d' := by rwa [← dist_eq_norm, dist_comm]
  linarith

/-- **The block chain of planar Brownian motion reaches the far set within `N` blocks**, uniformly in the
start `z ∈ closedBall 0 ρ`. -/
theorem planarBrownianMotion_not_reach_farSet_le {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (p : ℕ) :
    ∃ C : ℝ, ∀ {R ρ d' : ℝ}, 0 < R → 0 ≤ ρ → 0 < d' → ∀ {U : Set ℂ}, U ⊆ ball (0 : ℂ) R →
      ∀ z ∈ closedBall (0 : ℂ) ρ, ∀ s : ℝ, 0 < s → ∀ r : ℝ, 0 < r → r < 1 →
        4 * ((R + d' + ρ + 4 * s + 1) * r) ≤ s → ∀ N : ℕ, ⌊r ^ (-(2 + ζ))⌋₊ ≤ N + 1 →
          planarBrownianMotion z
              {ω : ContinuousPath ℂ |
                ¬ ∃ n ≤ N, ω (blockExitTimes s (farSet U d') n ω) ∈ farSet U d'} ≤
            ENNReal.ofReal (C * r ^ p) := by
  obtain ⟨C, hC⟩ := planarBrownianMotion_blockExit_avoid_frozen_superpoly hζ0 hζ1 p
  refine ⟨C, fun {R ρ d'} hR hρ hd' {U} hU z hz s hs r hr0 hr1 hars N hN => ?_⟩
  have hρz : ‖z‖ ≤ ρ := by simpa using hz
  have ha : 0 < R + d' + ρ + 4 * s + 1 := by linarith
  refine le_trans (measure_mono ?_)
    (hC z s hs (farSet U d') (closedBall (0 : ℂ) (R + d')) (R + d' + ρ + 4 * s + 1) r ha hr0 hr1
      hars (fun y hy => ?_))
  · intro ω hω n hn
    have hnN : n ≤ N := by omega
    have hF : ω (blockExitTimes s (farSet U d') n ω) ∉ farSet U d' := fun h => hω ⟨n, hnN, h⟩
    refine ⟨hF, ?_⟩
    by_contra hK
    exact hF (mem_farSet_of_ball_subset hU (by
      have : R + d' < ‖ω (blockExitTimes s (farSet U d') n ω)‖ := by simpa using hK
      exact this.le))
  · have hy' : ‖y‖ ≤ R + d' := by simpa using hy
    have : ‖y - z‖ ≤ ‖y‖ + ‖z‖ := norm_sub_le y z
    linarith

/-- The complement of the intersection of two events lies in the union of their complements. -/
theorem compl_reach_and_goodStop_subset {P Q : ContinuousPath ℂ → Prop} :
    {ω : ContinuousPath ℂ | P ω ∧ Q ω}ᶜ ⊆ {ω | ¬ P ω} ∪ {ω | ¬ Q ω} := by
  intro ω hω
  by_cases hP : P ω
  · exact Or.inr fun hQ => hω ⟨hP, hQ⟩
  · exact Or.inl hP

/-- **The Brownian side of the stopped-path comparison, uniformly in the start.** For `0 ≤ ρ < R`,
`ε, θ > 0`, `0 < ζ < 1` and `p` there are `(T, η, d)` with `η, d > 0` and `C` such that, for `U = ball 0 R`,
every start `z` in `closedBall 0 ρ`, every `d' > 0`, `s > 0`, `r ∈ (0, 1)` with
`4 (R + d' + ρ + 4 s + 1) r ≤ s` and every `N` with `⌊r ^ (-(2 + ζ))⌋ ≤ N + 1`, the probability that the
block chain does not reach `farSet U d'` within `N` blocks, or that the path is not a good stop, is at most
`C r ^ p + θ`.  The reach part alone holds for every `U ⊆ ball 0 R`. -/
theorem exists_planarBrownianMotion_reach_and_goodStop_compl_le {ρ R : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R)
    {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (p : ℕ) :
    ∃ (T η : ℝ≥0) (d C : ℝ), 0 < η ∧ 0 < d ∧ ∀ {d' : ℝ}, 0 < d' →
      ∀ z ∈ closedBall (0 : ℂ) ρ, ∀ s : ℝ, 0 < s → ∀ r : ℝ, 0 < r → r < 1 →
        4 * ((R + d' + ρ + 4 * s + 1) * r) ≤ s → ∀ N : ℕ, ⌊r ^ (-(2 + ζ))⌋₊ ≤ N + 1 →
          planarBrownianMotion z
              {ω : ContinuousPath ℂ |
                (∃ n ≤ N, ω (blockExitTimes s (farSet (ball (0 : ℂ) R) d') n ω) ∈
                    farSet (ball (0 : ℂ) R) d') ∧
                  GoodStop (ball (0 : ℂ) R) T η d ε ω}ᶜ ≤
            ENNReal.ofReal (C * r ^ p) + ENNReal.ofReal θ := by
  obtain ⟨T, η, hη, d, hd, hU⟩ := exists_forall_planarBrownianMotion_not_goodStop_lt hρ hρR hε hθ
  obtain ⟨C, hC⟩ := planarBrownianMotion_not_reach_farSet_le hζ0 hζ1 p
  have hR : 0 < R := lt_of_le_of_lt hρ hρR
  refine ⟨T, η, d, C, hη, hd, fun {d'} hd' z hz s hs r hr0 hr1 hars N hN => ?_⟩
  refine le_trans (measure_mono compl_reach_and_goodStop_subset) (le_trans (measure_union_le _ _) ?_)
  exact add_le_add (hC hR hρ hd' subset_rfl z hz s hs r hr0 hr1 hars N hN) (hU z hz).le

end BlockExit

end MatedCRT
