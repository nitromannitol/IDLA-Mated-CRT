import MatedCRT.FirstPass.S6j.LitUniformStartInvariance
import LatticeProb.Prob.ContinuousPathStepTimeCompare

/-!
# From the curve distance modulo parametrization to a pointwise bound

The uniform-start invariance principle (`MatedCRT.GMS21UniformStartInput`) compares the stopped embedded walk with
the stopped planar Brownian motion in the distance of curves modulo time parametrization,
`cmpEDist g f = inf_φ sup_t |g(t) - f(φ(t))|`. The displacement-time estimates of the proof of BG20 Lemma 6.9 use a
pointwise form: an increasing homeomorphism `ψ` of `[0, ∞)` with `|f(s) - g(ψ(s))| ≤ κ` for every `s`.

* `exists_orderIso_norm_sub_lt_of_cmpEDist_lt`: `cmpEDist g f < κ` gives such a `ψ` (with strict inequality).
* `stopAtExit_eq_self_of_exit_eq_top`, `stopAtExit_eq_min_of_exit_ne_top`: the two cases of the stopped path.
* `exists_orderIso_norm_sub_stopped_le_of_cmpEDist_lt`: if `b` leaves `U` at the finite time `T`, the pointwise
  bound for `b` stopped at `T`, in the form `|f(s) - b(min(ψ(s), T))| ≤ κ`.
* `exists_lt_stepTime_of_cmpEDist_lt_of_exit_eq_top`: if `b` never leaves `U`, an event of `f` before its `K`-th
  displacement time of size `s` transfers to `b` before its `K`-th displacement time of size `r ≥ 2s + 2κ`, at the
  cost `2κ` in the displacement (`LatticeProb.exists_lt_stepTime_of_norm_sub_comp_le`).
-/

open Set HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.CmpEDistPointwise

/-- **Pointwise form of the curve distance.** If the distance of curves modulo time parametrization from `g` to
`f` is less than `κ`, then some increasing homeomorphism `ψ` of `[0, ∞)` satisfies `|f(s) - g(ψ(s))| < κ` for
every `s`. -/
theorem exists_orderIso_norm_sub_lt_of_cmpEDist_lt {f g : ℝ≥0 → ℂ} {κ : ℝ}
    (h : cmpEDist g f < ENNReal.ofReal κ) :
    ∃ ψ : ℝ≥0 ≃o ℝ≥0, ∀ s, ‖f s - g (ψ s)‖ < κ := by
  unfold cmpEDist at h
  obtain ⟨φ, hφ⟩ := iInf_lt_iff.1 h
  refine ⟨φ.symm, fun s => ?_⟩
  have h1 : edist (g (φ.symm s)) (f (φ (φ.symm s))) < ENNReal.ofReal κ :=
    lt_of_le_of_lt (le_iSup (fun t => edist (g t) (f (φ t))) (φ.symm s)) hφ
  rw [OrderIso.apply_symm_apply, edist_lt_ofReal, dist_comm, dist_eq_norm] at h1
  exact h1

/-- A path that never leaves `U` is its own stopped path. -/
theorem stopAtExit_eq_self_of_exit_eq_top {U : Set ℂ} {b : ℝ≥0 → ℂ} (h : pathExitTime U b = ⊤) :
    stopAtExit U b = b := by
  funext t
  simp [stopAtExit, h]

/-- A path that leaves `U` at the finite time `T` is, once stopped, `t ↦ b(min(t, T))`. -/
theorem stopAtExit_eq_min_of_exit_ne_top {U : Set ℂ} {b : ℝ≥0 → ℂ} (h : pathExitTime U b ≠ ⊤) (t : ℝ≥0) :
    stopAtExit U b t = b (min t (pathExitTime U b).toNNReal) := by
  simp [stopAtExit, h]

/-- **Pointwise bound against the stopped path.** If `b` leaves `U` at a finite time `T` and the stopped path is
within curve distance `κ` of `f`, then `|f(s) - b(min(ψ(s), T))| ≤ κ` for every `s`, for some increasing
homeomorphism `ψ` of `[0, ∞)`. -/
theorem exists_orderIso_norm_sub_stopped_le_of_cmpEDist_lt {U : Set ℂ} {f b : ℝ≥0 → ℂ} {κ : ℝ}
    (hexit : pathExitTime U b ≠ ⊤) (h : cmpEDist (stopAtExit U b) f < ENNReal.ofReal κ) :
    ∃ ψ : ℝ≥0 ≃o ℝ≥0, ∀ s, ‖f s - b (min (ψ s) (pathExitTime U b).toNNReal)‖ ≤ κ := by
  obtain ⟨ψ, hψ⟩ := exists_orderIso_norm_sub_lt_of_cmpEDist_lt h
  refine ⟨ψ, fun s => ?_⟩
  rw [← stopAtExit_eq_min_of_exit_ne_top hexit]
  exact (hψ s).le

/-- **Transfer of a displacement event when the Brownian path does not exit.** If `b` never leaves `U`, its
stopped path is within curve distance `κ` of `f`, and `f` reaches distance `a` from `f 0` strictly before its `K`-th
displacement time of size `s`, then `b` reaches distance `a - 2κ` from `b 0` strictly before its `K`-th
displacement time of size `r`, whenever `2s + 2κ ≤ r`. -/
theorem exists_lt_stepTime_of_cmpEDist_lt_of_exit_eq_top {U : Set ℂ} {f b : ℝ≥0 → ℂ} {κ s r a : ℝ}
    (hexit : pathExitTime U b = ⊤) (h : cmpEDist (stopAtExit U b) f < ENNReal.ofReal κ)
    (hr : 2 * s + 2 * κ ≤ r) {K : ℕ}
    (hf : ∃ t : ℝ≥0, (t : ℝ≥0∞) < LatticeProb.stepTime f s K ∧ a ≤ ‖f t - f 0‖) :
    ∃ t : ℝ≥0, (t : ℝ≥0∞) < LatticeProb.stepTime b r K ∧ a - 2 * κ ≤ ‖b t - b 0‖ := by
  rw [stopAtExit_eq_self_of_exit_eq_top hexit] at h
  obtain ⟨ψ, hψ⟩ := exists_orderIso_norm_sub_lt_of_cmpEDist_lt h
  exact LatticeProb.exists_lt_stepTime_of_norm_sub_comp_le ψ (fun t => (hψ t).le) hr hf

end MatedCRT.CmpEDistPointwise
