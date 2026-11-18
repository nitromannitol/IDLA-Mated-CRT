import MatedCRT.FirstPass.Derived.BrownianBlockExitTimes
import MatedCRT.FirstPass.Derived.PlanarChainInBall

/-!
# Tightness of the number of block exits of planar Brownian motion

For `0 < ζ < 1` and `p ∈ ℕ` there is `C` such that, for planar Brownian motion started at any
`z`, any mesh `s > 0`, any frozen set `F`, any set `K` of points at distance less than `a - 4 s`
from `z`, any `0 < r < 1` and any separation `c ≥ 2 a r`, the probability that the first
`K_r = ⌊r ^ -(2 + ζ)⌋` block exits are `c`-separated with all the positions `B_{σ_n}`, `n < K_r`,
in `K` is at most `C r ^ p`. This is the Brownian half of the tightness of the number of steps
(step T4) in the chaining of the proof of Theorem 3.10 of the Gwynne-Miller-Sheffield invariance
principle: between consecutive exits the path stays within `4 s` of the earlier exit position, so on
this event the path stays in the ball of radius `a` around `z` up to the `K_r`-th exit, and the
separated-chain estimate for planar Brownian motion applies.

## Main results

* `planarBrownianMotion_blockExit_separated_superpoly`: the bound on path space.
* `map_blockExitPositions_separated_superpoly`: the same bound for the law of the block-exit
  positions `(B_{σ_0}, …, B_{σ_{K_r}})`, on the event that the history has `c`-separated increments
  and its first `K_r` entries in `K`.
-/

set_option autoImplicit false

open MeasureTheory Set MarkovProcess
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

/-- For `0 < r < 1` and `ζ > 0` the number of steps `⌊r ^ -(2 + ζ)⌋` is positive. -/
theorem floor_rpow_neg_pos {ζ : ℝ} (hζ0 : 0 < ζ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    0 < ⌊r ^ (-(2 + ζ))⌋₊ :=
  Nat.floor_pos.2 (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr0 hr1.le (by linarith))

/-- **Tightness of the number of block exits, path form.** -/
theorem planarBrownianMotion_blockExit_separated_superpoly {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (p : ℕ) :
    ∃ C : ℝ, ∀ (z : ℂ) (s : ℝ), 0 < s → ∀ (F K : Set ℂ) (a c r : ℝ), 0 < a → 0 < r → r < 1 →
      2 * (a * r) ≤ c → (∀ y ∈ K, ‖y - z‖ < a - 4 * s) →
      planarBrownianMotion z {ω | ∀ n < ⌊r ^ (-(2 + ζ))⌋₊,
          c ≤ ‖ω (blockExitTimes s F (n + 1) ω) - ω (blockExitTimes s F n ω)‖ ∧
          ω (blockExitTimes s F n ω) ∈ K}
        ≤ ENNReal.ofReal (C * r ^ p) := by
  obtain ⟨C, hC⟩ :=
    PlanarChainInBall.planarBrownianMotion_separated_chain_in_ball_superpoly hζ0 hζ1 p
  refine ⟨C, fun z s hs F K a c r ha hr0 hr1 hac hK => ?_⟩
  refine le_trans (measure_mono ?_) (hC z a ha r hr0 hr1)
  intro ω hω
  have hω' : ∀ n < ⌊r ^ (-(2 + ζ))⌋₊,
      c ≤ ‖ω (blockExitTimes s F (n + 1) ω) - ω (blockExitTimes s F n ω)‖ ∧
        ω (blockExitTimes s F n ω) ∈ K := hω
  refine ⟨fun n => blockExitTimes s F n ω, monotone_blockExitTimes s F ω,
    fun n hn => hac.trans (hω' n hn).1, fun t ht => ?_⟩
  obtain ⟨n, hn, h⟩ := exists_norm_sub_le_of_le_blockExitTimes hs F _ ω ht
    (floor_rpow_neg_pos hζ0 hr0 hr1)
  have h2 := hK _ (hω' n hn).2
  calc ‖ω t - z‖ ≤ ‖ω t - ω (blockExitTimes s F n ω)‖ + ‖ω (blockExitTimes s F n ω) - z‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < a := by linarith

/-- The histories of length `N + 1` whose `N` increments have modulus at least `c` and whose first
`N` entries lie in `K`. -/
def separatedHistories (N : ℕ) (c : ℝ) (K : Set ℂ) : Set (Fin (N + 1) → ℂ) :=
  {h | ∀ n : Fin N, c ≤ ‖h n.succ - h n.castSucc‖ ∧ h n.castSucc ∈ K}

theorem measurableSet_separatedHistories (N : ℕ) (c : ℝ) {K : Set ℂ} (hK : MeasurableSet K) :
    MeasurableSet (separatedHistories N c K) := by
  have e : separatedHistories N c K =
      ⋂ n : Fin N, ({h : Fin (N + 1) → ℂ | c ≤ ‖h n.succ - h n.castSucc‖} ∩
        (fun h : Fin (N + 1) → ℂ => h n.castSucc) ⁻¹' K) := by
    ext h
    simp [separatedHistories]
  rw [e]
  refine MeasurableSet.iInter fun n => MeasurableSet.inter ?_ (hK.preimage (measurable_pi_apply _))
  have hm : Measurable fun h : Fin (N + 1) → ℂ => ‖h n.succ - h n.castSucc‖ := by fun_prop
  exact measurableSet_le measurable_const hm

/-- **Tightness of the number of block exits, law of the block-exit positions.** Under planar
Brownian motion started at `z`, the history `(B_{σ_0}, …, B_{σ_{K_r}})`, `K_r = ⌊r ^ -(2 + ζ)⌋`, has
`c`-separated increments and its first `K_r` entries in `K` with probability at most `C r ^ p`. -/
theorem map_blockExitPositions_separated_superpoly {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (p : ℕ) :
    ∃ C : ℝ, ∀ (z : ℂ) (s : ℝ), 0 < s → ∀ (F K : Set ℂ), MeasurableSet F → MeasurableSet K →
      ∀ (a c r : ℝ), 0 < a → 0 < r → r < 1 →
      2 * (a * r) ≤ c → (∀ y ∈ K, ‖y - z‖ < a - 4 * s) →
      (planarBrownianMotion z).map (blockExitPositions s F ⌊r ^ (-(2 + ζ))⌋₊)
          (separatedHistories ⌊r ^ (-(2 + ζ))⌋₊ c K)
        ≤ ENNReal.ofReal (C * r ^ p) := by
  obtain ⟨C, hC⟩ := planarBrownianMotion_blockExit_separated_superpoly hζ0 hζ1 p
  refine ⟨C, fun z s hs F K hF hKm a c r ha hr0 hr1 hac hK => ?_⟩
  rw [Measure.map_apply (measurable_blockExitPositions s hF _)
    (measurableSet_separatedHistories _ c hKm)]
  refine le_trans (measure_mono ?_) (hC z s hs F K a c r ha hr0 hr1 hac hK)
  intro ω hω n hn
  have h := hω ⟨n, hn⟩
  rw [blockExitPositions_apply, blockExitPositions_apply] at h
  exact h

end BlockExit

end MatedCRT
