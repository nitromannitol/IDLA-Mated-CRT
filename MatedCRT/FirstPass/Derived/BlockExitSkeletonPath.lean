import MatedCRT.FirstPass.Derived.BrownianBlockExitTimes
import MatedCRT.FirstPass.Derived.CmpEDistKnots

/-!
# Paths reconstructed from their block-exit skeletons

The step reconstruction `stepPath N h` of a history `h : Fin (N + 1) → ℂ` is the path equal to
`h n` on `[n, n + 1)` for `n < N` and to `h N` from time `N` on. It is `1`-Lipschitz from the sup
distance of histories to the distance `cmpEDist` of curves modulo time parametrization.

A path `ω` stopped at its `N`-th block-exit time is within `8 s` (for `cmpEDist`) of the step
reconstruction of its block-exit positions, as soon as the block-exit chain is frozen in `F` by
step `N` and the block-exit times before freezing are strictly increasing. This is the Brownian half
of step T5 of the chaining in the proof of Theorem 3.10 of Gwynne-Miller-Sheffield
(arXiv:1807.07515): the oscillation between consecutive block exits is at most `4 s`
(`norm_sub_le_of_blockExitTimes_le`), and the knot comparison `cmpEDist_le_of_finite_knots` matches
the block-exit times with the integer times of the reconstruction.

## Main statements

* `stepPath`, `cmpEDist_stepPath_le`: the reconstruction and its Lipschitz bound.
* `blockExitTimes_eq_of_mem`: once a block-exit position lies in `F`, the block-exit times stay put.
* `cmpEDist_stoppedAtBlockExit_stepPath_le`: the stopped path is within `8 s` of the reconstruction
  of its block-exit positions.
-/

open MeasureTheory Set Metric MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

namespace BlockExit

/-- The step reconstruction of a history `h : Fin (N + 1) → ℂ`: the path equal to `h n` on
`[n, n + 1)` for `n < N` and to `h N` on `[N, ∞)`. -/
noncomputable def stepPath (N : ℕ) (h : Fin (N + 1) → ℂ) (t : ℝ≥0) : ℂ :=
  h ⟨min ⌊t⌋₊ N, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- The step reconstruction is `1`-Lipschitz from the sup distance of histories to the distance
`cmpEDist` of curves modulo time parametrization. -/
theorem cmpEDist_stepPath_le (N : ℕ) (h h' : Fin (N + 1) → ℂ) :
    cmpEDist (stepPath N h) (stepPath N h') ≤ edist h h' := by
  unfold cmpEDist
  refine (iInf_le _ (OrderIso.refl ℝ≥0)).trans (iSup_le fun t => ?_)
  exact edist_le_pi_edist h h' _

/-- Value of the step reconstruction at a time `t ∈ [n, n + 1)` with `n ≤ N`. -/
theorem stepPath_of_mem_Ico {N n : ℕ} (hn : n ≤ N) (h : Fin (N + 1) → ℂ) {t : ℝ≥0}
    (ht : t ∈ Ico (n : ℝ≥0) ((n + 1 : ℕ) : ℝ≥0)) :
    stepPath N h t = h ⟨n, Nat.lt_succ_of_le hn⟩ := by
  have hfl : ⌊t⌋₊ = n := (Nat.floor_eq_iff (by positivity)).mpr ⟨ht.1, by exact_mod_cast ht.2⟩
  simp only [stepPath, hfl, min_eq_left hn]

/-- **Freezing.** Once the block-exit position `ω (σ_M ω)` lies in `F`, all later block-exit times
equal `σ_M ω`. -/
theorem blockExitTimes_eq_of_mem (s : ℝ) {F : Set ℂ} {M : ℕ} {ω : ContinuousPath ℂ}
    (hM : ω (blockExitTimes s F M ω) ∈ F) :
    ∀ k, M ≤ k → blockExitTimes s F k ω = blockExitTimes s F M ω := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k _ ih =>
    have h0 : ContinuousPath.shift (blockExitTimes s F M ω) ω 0 ∈ F := by
      rw [ContinuousPath.shift_apply, add_zero]
      exact hM
    rw [blockExitTimes_succ', ih]
    simp only [firstBlockExitTime, h0, ↓reduceIte, add_zero]

/-- **Stopped path versus the reconstruction of its block-exit positions.** Let `0 < s`, `M ≤ N`,
let the block-exit times `σ_0 < σ_1 < ⋯ < σ_M` be strictly increasing, and let `ω (σ_M ω) ∈ F`.
Then the path `ω` stopped at `σ_N ω` is within `8 s`, modulo time parametrization, of the step
reconstruction of its block-exit positions `(ω (σ_0 ω), …, ω (σ_N ω))`. -/
theorem cmpEDist_stoppedAtBlockExit_stepPath_le {s : ℝ} (hs : 0 < s) (F : Set ℂ) {M N : ℕ}
    (hMN : M ≤ N) (ω : ContinuousPath ℂ)
    (hstrict : ∀ n < M, blockExitTimes s F n ω < blockExitTimes s F (n + 1) ω)
    (hM : ω (blockExitTimes s F M ω) ∈ F) :
    cmpEDist (fun t => ω (min t (blockExitTimes s F N ω)))
        (stepPath N (blockExitPositions s F N ω)) ≤ ENNReal.ofReal (4 * s + 0 + 4 * s) := by
  have hfrz := blockExitTimes_eq_of_mem s hM
  have hNM : blockExitTimes s F N ω = blockExitTimes s F M ω := hfrz N hMN
  have hs4 : (0 : ℝ) ≤ 4 * s := by linarith
  refine CmpEDistKnots.cmpEDist_le_of_finite_knots (τ := fun n => blockExitTimes s F n ω)
    (σ := fun n => (n : ℝ≥0)) (p := fun n => ω (blockExitTimes s F n ω))
    (q := fun n => ω (blockExitTimes s F n ω)) (N := M) hstrict
    (fun n _ => by push_cast; exact lt_add_one _) rfl (by simp)
    (fun n _ => (dist_self _).le) ?_ ?_ ?_ ?_
  · intro n hn t ht
    have hle : t ≤ blockExitTimes s F N ω :=
      ht.2.le.trans ((monotone_blockExitTimes s F ω (Nat.succ_le_of_lt hn)).trans
        (monotone_blockExitTimes s F ω hMN))
    simp only [min_eq_left hle]
    rw [dist_eq_norm]
    exact norm_sub_le_of_blockExitTimes_le hs F n ω ht.1 ht.2.le
  · intro n hn t ht
    rw [stepPath_of_mem_Ico ((hn.trans_le hMN).le) _ ht, blockExitPositions_apply, dist_self]
    exact hs4
  · intro t ht
    have hle : blockExitTimes s F N ω ≤ t := hNM.le.trans ht
    rw [min_eq_right hle, hNM, dist_self]
    exact hs4
  · intro t ht
    have hkM : M ≤ min ⌊t⌋₊ N :=
      le_min (Nat.le_floor ht) hMN
    simp only [stepPath, blockExitPositions_apply]
    rw [hfrz _ hkM, dist_self]
    exact hs4

end BlockExit

end MatedCRT
