import MatedCRT.FirstPass.Derived.BlockExitSkeletonPath
import MatedCRT.FirstPass.Derived.BrownianBlockExitFrozenHit

/-!
# The Brownian path is close to the reconstruction of its block-exit skeleton

Along a path with unbounded range the block-exit times strictly increase as long as the
block-exit position is off the frozen set `F` (each such block exit moves the path by more than
`s / 2`). Hence, as soon as some block-exit position among the first `N + 1` lies in `F`, the path
stopped at its `N`-th block exit is within `8 s` (for `cmpEDist`) of the step reconstruction of its
block-exit positions (`cmpEDist_stoppedAtBlockExit_stepPath_le`).

Under planar Brownian motion the range is almost surely unbounded, and the chain of the first
`⌊r ^ (-(2 + ζ))⌋` block-exit positions avoids `F` (with `Fᶜ` in a ball of radius `a - 4 s` around
the start and `4 a r ≤ s`) with probability at most `C r ^ p`
(`planarBrownianMotion_blockExit_avoid_frozen_superpoly`). So the stopped Brownian path is within
any `a' > 8 s` of the reconstruction of its block-exit skeleton outside an event of probability at
most `C r ^ p`. This is the Brownian good event of step T5 of the chaining in the proof of
Theorem 3.10 of Gwynne-Miller-Sheffield (arXiv:1807.07515).

## Main statements

* `blockExitTimes_lt_succ_of_not_mem`: strict increase of the block-exit times off `F`.
* `cmpEDist_stoppedAtBlockExit_stepPath_le_of_exists_mem`: the skeleton approximation along a path
  with unbounded range whose block-exit chain meets `F` by step `N`.
* `planarBrownianMotion_cmpEDist_stoppedAtBlockExit_stepPath_superpoly`: the probability bound.
-/

open MeasureTheory Set Metric MarkovProcess
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

/-- Along a path with unbounded range, the block-exit times strictly increase as long as the
block-exit position is off the frozen set. -/
theorem blockExitTimes_lt_succ_of_not_mem {s : ℝ} (hs : 0 < s) {F : Set ℂ}
    {ω : ContinuousPath ℂ} (hω : ¬ Bornology.IsBounded (range ω)) (n : ℕ)
    (hn : ω (blockExitTimes s F n ω) ∉ F) :
    blockExitTimes s F n ω < blockExitTimes s F (n + 1) ω := by
  refine lt_of_le_of_ne (blockExitTimes_le_succ s F n ω) fun heq => ?_
  have h := half_lt_norm_blockExit_step hs hω n hn
  rw [heq, sub_self, norm_zero] at h
  linarith

/-- **Skeleton approximation along a path with unbounded range.** If some block-exit position
among the first `N + 1` lies in the frozen set, the path stopped at its `N`-th block exit is within
`8 s` of the step reconstruction of its block-exit positions. -/
theorem cmpEDist_stoppedAtBlockExit_stepPath_le_of_exists_mem {s : ℝ} (hs : 0 < s) {F : Set ℂ}
    {N : ℕ} {ω : ContinuousPath ℂ} (hω : ¬ Bornology.IsBounded (range ω))
    (hF : ∃ n ≤ N, ω (blockExitTimes s F n ω) ∈ F) :
    cmpEDist (fun t => ω (min t (blockExitTimes s F N ω)))
        (stepPath N (blockExitPositions s F N ω)) ≤ ENNReal.ofReal (4 * s + 0 + 4 * s) := by
  classical
  have hM : Nat.find hF ≤ N ∧ ω (blockExitTimes s F (Nat.find hF) ω) ∈ F := Nat.find_spec hF
  refine cmpEDist_stoppedAtBlockExit_stepPath_le hs F hM.1 ω (fun n hn => ?_) hM.2
  refine blockExitTimes_lt_succ_of_not_mem hs hω n fun hmem => ?_
  exact Nat.find_min hF hn ⟨(lt_of_lt_of_le hn hM.1).le, hmem⟩

/-- **The Brownian good event of the skeleton approximation.** For `0 < ζ < 1` and every `p` there
is `C` such that for every start `z`, mesh `s > 0`, frozen set `F` whose complement lies at
distance less than `a - 4 s` from `z`, and `0 < r < 1` with `4 a r ≤ s`, planar Brownian motion
from `z`, stopped at its `N`-th block exit, `N = ⌊r ^ (-(2 + ζ))⌋`, is within `a'` of the step
reconstruction of its block-exit positions, for every `a' > 8 s`, outside an event of probability
at most `C r ^ p`. -/
theorem planarBrownianMotion_cmpEDist_stoppedAtBlockExit_stepPath_superpoly {ζ : ℝ}
    (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (p : ℕ) :
    ∃ C : ℝ, ∀ (z : ℂ) (s : ℝ), 0 < s → ∀ (F : Set ℂ) (a r : ℝ), 0 < a → 0 < r → r < 1 →
      4 * (a * r) ≤ s → (∀ y ∉ F, ‖y - z‖ < a - 4 * s) → ∀ a' : ℝ, 8 * s < a' →
      planarBrownianMotion z {ω | ¬ cmpEDist
          (fun t => ω (min t (blockExitTimes s F ⌊r ^ (-(2 + ζ))⌋₊ ω)))
          (stepPath ⌊r ^ (-(2 + ζ))⌋₊ (blockExitPositions s F ⌊r ^ (-(2 + ζ))⌋₊ ω))
          < ENNReal.ofReal a'}
        ≤ ENNReal.ofReal (C * r ^ p) := by
  obtain ⟨C, hC⟩ := planarBrownianMotion_blockExit_avoid_frozen_superpoly hζ0 hζ1 p
  refine ⟨C, fun z s hs F a r ha hr0 hr1 hars hF a' ha' => ?_⟩
  refine le_trans (measure_mono_ae ?_)
    (hC z s hs F Fᶜ a r ha hr0 hr1 hars fun y hy => hF y hy)
  filter_upwards [ae_planarBrownianMotion_unbounded_range z] with ω hω hbad
  have hlt : ENNReal.ofReal (4 * s + 0 + 4 * s) < ENNReal.ofReal a' :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  have hnot : ∀ n < ⌊r ^ (-(2 + ζ))⌋₊, ω (blockExitTimes s F n ω) ∉ F := fun n hn hmem =>
    hbad (lt_of_le_of_lt
      (cmpEDist_stoppedAtBlockExit_stepPath_le_of_exists_mem hs hω ⟨n, hn.le, hmem⟩) hlt)
  exact fun n hn => ⟨hnot n hn, hnot n hn⟩

end BlockExit

end MatedCRT
