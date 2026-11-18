import MatedCRT.FirstPass.Derived.BlockExitSkeletonGood
import MatedCRT.FirstPass.Derived.UniformStartStopTransfer
import MatedCRT.FirstPass.Derived.StopAtExitNested

/-!
# The path stopped at its exit time versus the block-exit skeleton

Deterministic join between the path `ω` stopped at its exit time from an open set `U` (the stopping
used in the uniform-start invariance principle) and the step reconstruction of its block-exit
positions, the skeleton on which the Prokhorov comparison of the chaining is carried out.

* `cmpEDist_stopAtExit_le_of_forall_dist_le`: if the path exits `U` before time `σ`, the path
  stopped at its exit time from `U` is within `D` (modulo time parametrization) of the path
  stopped at `σ`, provided that `ω` stays within `D` of its exit point on `[τ, σ]`.
* `exists_blockIndex_of_le`: for `u ≤ σ_N` the largest block index `k` with `σ_k ≤ u` has
  `ω u` within `c` of `ω (σ_k)`, when the path oscillates by at most `c` on each block interval.
* `cmpEDist_stopAtExit_stepPath_le_of_skeleton`: freezing the block chain on the complement of `U`,
  if the chain reaches the complement within `N` steps and every block position that is within
  `4 s` of the complement stays within `D` of itself at all later block positions up to `N`
  (a condition on the skeleton alone), then the path stopped at its exit time from `U` is within
  `(8 s + D) + 8 s` of the step reconstruction of its block-exit positions.
-/

set_option autoImplicit false

open MeasureTheory Set Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

open MatedCRT.StopAtExitCmp

/-- **Stopped at the exit time versus stopped at a later time.** If the path `ω` leaves `U` at a time
`τ ≤ σ` and stays within `D` of its exit point `ω τ` on `[τ, σ]`, then `ω` stopped at its exit time
from `U` is within `D`, modulo time parametrization, of `ω` stopped at `σ`. -/
theorem cmpEDist_stopAtExit_le_of_forall_dist_le {U : Set ℂ} {ω : ℝ≥0 → ℂ} {σ : ℝ≥0} {D : ℝ}
    (hτσ : pathExitTime U ω ≤ σ)
    (hD : ∀ u : ℝ≥0, (pathExitTime U ω).toNNReal ≤ u → u ≤ σ →
      dist (ω u) (ω (pathExitTime U ω).toNNReal) ≤ D) :
    cmpEDist (stopAtExit U ω) (fun t => ω (min t σ)) ≤ ENNReal.ofReal D := by
  have hfin : pathExitTime U ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hτσ
  have hτ' : ((pathExitTime U ω).toNNReal : ℝ≥0∞) = pathExitTime U ω := ENNReal.coe_toNNReal hfin
  have hτσ' : (pathExitTime U ω).toNNReal ≤ σ := by
    rw [← hτ'] at hτσ
    exact_mod_cast hτσ
  refine (cmpEDist_le_iSup_edist _ _).trans (iSup_le fun t => ?_)
  have hstop : stopAtExit U ω t = ω (min t (pathExitTime U ω).toNNReal) := by
    simp [stopAtExit, hfin]
  rw [hstop]
  by_cases ht : t ≤ (pathExitTime U ω).toNNReal
  · rw [min_eq_left ht, min_eq_left (ht.trans hτσ'), edist_self]
    exact zero_le
  · have ht' := not_le.1 ht
    rw [min_eq_right ht'.le, edist_dist]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := hD (min t σ) (le_min ht'.le hτσ') (min_le_right _ _)
    rwa [dist_comm]

/-- **The block containing a time.** If `σ` is a nondecreasing sequence of times with `σ 0 = 0`,
`ω` oscillates by at most `c ≥ 0` from `ω (σ n)` on `[σ n, σ (n+1)]` for `n < N`, and `u ≤ σ N`,
then the largest index `k ≤ N` with `σ k ≤ u` satisfies `dist (ω u) (ω (σ k)) ≤ c`. -/
theorem exists_blockIndex_of_le {σ : ℕ → ℝ≥0} {N : ℕ} {ω : ℝ≥0 → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h0 : σ 0 = 0)
    (hosc : ∀ n < N, ∀ t : ℝ≥0, σ n ≤ t → t ≤ σ (n + 1) → dist (ω t) (ω (σ n)) ≤ c)
    {u : ℝ≥0} (hu : u ≤ σ N) :
    ∃ k ≤ N, σ k ≤ u ∧ dist (ω u) (ω (σ k)) ≤ c ∧ ∀ l ≤ N, σ l ≤ u → l ≤ k := by
  classical
  have hspec : σ (Nat.findGreatest (fun k => σ k ≤ u) N) ≤ u :=
    Nat.findGreatest_spec (P := fun k => σ k ≤ u) (Nat.zero_le N) (by rw [h0]; exact zero_le)
  refine ⟨Nat.findGreatest (fun k => σ k ≤ u) N, Nat.findGreatest_le N, hspec, ?_,
    fun l hl hlu => Nat.le_findGreatest hl hlu⟩
  set k := Nat.findGreatest (fun k => σ k ≤ u) N with hk
  by_cases hkN : k < N
  · have hnot : ¬ σ (k + 1) ≤ u :=
      Nat.findGreatest_is_greatest (P := fun k => σ k ≤ u) (Nat.lt_succ_self k) hkN
    exact hosc k hkN u hspec (not_le.1 hnot).le
  · have hkeq : k = N := le_antisymm (Nat.findGreatest_le N) (not_lt.1 hkN)
    have hueq : u = σ k := by rw [hkeq]; exact le_antisymm hu (hkeq ▸ hspec)
    rw [hueq, dist_self]
    exact hc

/-- **Stopped at the exit time versus the block-exit skeleton.** Let `0 < s`, `U` open, the block chain
frozen on `Uᶜ`, and suppose that the chain reaches `Uᶜ` within `N` steps. If every block-exit position
within `4 s` of `Uᶜ` stays within `D` of itself at all later block-exit positions `σ_n`, `n ≤ N` (a
condition on the skeleton `(ω (σ_0), …, ω (σ_N))` alone), then the path `ω` stopped at its exit time
from `U` is within `(8 s + D) + 8 s`, modulo time parametrization, of the step reconstruction of its
block-exit positions. -/
theorem cmpEDist_stopAtExit_stepPath_le_of_skeleton {s : ℝ} (hs : 0 < s) {U : Set ℂ}
    (hU : IsOpen U) {N : ℕ} {ω : ContinuousPath ℂ} {D : ℝ}
    (hF : ∃ n ≤ N, ω (blockExitTimes s Uᶜ n ω) ∈ Uᶜ)
    (hreg : ∀ j n : ℕ, j ≤ n → n ≤ N →
      (∃ w, w ∉ U ∧ dist (ω (blockExitTimes s Uᶜ j ω)) w ≤ 4 * s) →
      dist (ω (blockExitTimes s Uᶜ n ω)) (ω (blockExitTimes s Uᶜ j ω)) ≤ D) :
    cmpEDist (stopAtExit U ω) (stepPath N (blockExitPositions s Uᶜ N ω)) ≤
      ENNReal.ofReal (8 * s + D) + ENNReal.ofReal (4 * s + 0 + 4 * s) := by
  classical
  obtain ⟨hMN, hM⟩ : Nat.find hF ≤ N ∧ ω (blockExitTimes s Uᶜ (Nat.find hF) ω) ∈ Uᶜ :=
    Nat.find_spec hF
  have hσN : blockExitTimes s Uᶜ N ω = blockExitTimes s Uᶜ (Nat.find hF) ω :=
    blockExitTimes_eq_of_mem s hM N hMN
  have hτM : pathExitTime U ω ≤ ((blockExitTimes s Uᶜ N ω : ℝ≥0) : ℝ≥0∞) := by
    rw [hσN]
    exact exitTime_le_of_not_mem hM
  have hfin : pathExitTime U ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hτM
  have hτ' : ((pathExitTime U ω).toNNReal : ℝ≥0∞) = pathExitTime U ω := ENNReal.coe_toNNReal hfin
  have hτ'N : (pathExitTime U ω).toNNReal ≤ blockExitTimes s Uᶜ N ω := by
    rw [← hτ'] at hτM
    exact_mod_cast hτM
  have hout : ω (pathExitTime U ω).toNNReal ∉ U := not_mem_at_exitTime hU ω.continuous hfin
  have hosc : ∀ n < N, ∀ t : ℝ≥0, blockExitTimes s Uᶜ n ω ≤ t → t ≤ blockExitTimes s Uᶜ (n + 1) ω →
      dist (ω t) (ω (blockExitTimes s Uᶜ n ω)) ≤ 4 * s := fun n _ t h1 h2 => by
    rw [dist_eq_norm]
    exact norm_sub_le_of_blockExitTimes_le hs Uᶜ n ω h1 h2
  have hblock := fun u (hu : u ≤ blockExitTimes s Uᶜ N ω) =>
    exists_blockIndex_of_le (σ := fun n => blockExitTimes s Uᶜ n ω) (N := N) (ω := ⇑ω)
      (by linarith) (blockExitTimes_zero s Uᶜ ω) hosc hu
  obtain ⟨j, hjN, hjτ, hjd, -⟩ := hblock _ hτ'N
  have hD : ∀ u : ℝ≥0, (pathExitTime U ω).toNNReal ≤ u → u ≤ blockExitTimes s Uᶜ N ω →
      dist (ω u) (ω (pathExitTime U ω).toNNReal) ≤ 8 * s + D := by
    intro u hu1 hu2
    obtain ⟨k, hkN, hku, hkd, hmax⟩ := hblock u hu2
    have hjk : j ≤ k := hmax j hjN (hjτ.trans hu1)
    have hr := hreg j k hjk hkN ⟨ω (pathExitTime U ω).toNNReal, hout, by rwa [dist_comm]⟩
    calc dist (ω u) (ω (pathExitTime U ω).toNNReal)
        ≤ dist (ω u) (ω (blockExitTimes s Uᶜ k ω)) +
            dist (ω (blockExitTimes s Uᶜ k ω)) (ω (blockExitTimes s Uᶜ j ω)) +
            dist (ω (blockExitTimes s Uᶜ j ω)) (ω (pathExitTime U ω).toNNReal) :=
          dist_triangle4 _ _ _ _
      _ ≤ 8 * s + D := by
          have := dist_comm (ω (blockExitTimes s Uᶜ j ω)) (ω (pathExitTime U ω).toNNReal)
          linarith
  have h1 := cmpEDist_stopAtExit_le_of_forall_dist_le hτM hD
  have h2 := cmpEDist_stoppedAtBlockExit_stepPath_le_of_exists_mem hs hF
  exact (cmpEDist_triangle _ _ _).trans (add_le_add h1 h2)

end BlockExit

end MatedCRT
