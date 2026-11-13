import MatedCRT.FirstPass.Derived.ExitTimeNoShortTravel

/-!
# No short travel of the walk in the plane: the Euclidean form of BG20 Proposition 6.5

Let `v : ℤ → ℂ` be a vertex embedding, `A y ⊆ ℤ` the region attached to a vertex `y` and `Y ⊆ ℤ` the
set whose exit time `τ_Y` stops the walk.  `NoShortTravel A Y g x`
(`MatedCRT/FirstPass/Derived/ExitTimeNoShortTravel.lean`) says that two times `s < t ≤ τ_Y` with
`t < s + g` are linked by at most one crossing of a region.  If every region `A y` (`y ∈ Y`) lies in the
closed `v`-ball of radius `δ` about `v y` and each step of the path before `τ_Y` moves `v` by at most
`J`, the chain `X_s ∈ A (X_p)`, `X_{q-1} ∈ A (X_p)`, `X_q`, `X_t ∈ A (X_q)` gives
`|v (X_s) - v (X_t)| ≤ δ + δ + J + δ`.

* `dist_le_of_noShortTravel`: the deterministic bound `|v (X_s) - v (X_t)| ≤ 3 δ + J`;
* `srwLaw_exists_shortTravel_le`: for simple random walk on a multigraph `m` whose edges out of `Y`
  have `v`-length at most `J`, the probability of a travel of length more than `3 δ + J` in fewer
  than `g` steps before `τ_Y` is at most `ψ₀ + K q` (BG20 Proposition 6.5, with the bound (6.36) and
  Lemma 6.11 as the hypotheses of `srwLaw_not_noShortTravel_le`).
-/

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRT.FirstPass.Derived

open SuccessiveExitGaps

/-- **Euclidean consequence of no short travel.**  If every region `A y` with `y ∈ Y` lies in the
closed `v`-ball of radius `δ` about `v y` and every step of `x` before `τ_Y` moves `v` by at most `J`,
then on `NoShortTravel A Y g x` two times `s < t ≤ τ_Y` with `t < s + g` satisfy
`|v (x s) - v (x t)| ≤ 3 δ + J`. -/
theorem dist_le_of_noShortTravel {A : ℤ → Set ℤ} {Y : Set ℤ} {g : ℕ} {x : ℕ → ℤ} {v : ℤ → ℂ}
    {δ J : ℝ} (hA : ∀ y ∈ Y, ∀ z ∈ A y, dist (v z) (v y) ≤ δ)
    (hjump : ∀ n : ℕ, (n : ℕ∞) < vExitTime Y x → dist (v (x n)) (v (x (n + 1))) ≤ J)
    (hx : NoShortTravel A Y g x) {s t : ℕ} (hst : s < t) (htg : t < s + g)
    (ht : (t : ℕ∞) ≤ vExitTime Y x) :
    dist (v (x s)) (v (x t)) ≤ 3 * δ + J := by
  have hlt : ∀ n : ℕ, n < t → (n : ℕ∞) < vExitTime Y x := fun n hn => by
    have hn' : (n : ℕ∞) < (t : ℕ∞) := by exact_mod_cast hn
    exact lt_of_lt_of_le hn' ht
  have hmemY : ∀ n : ℕ, n < t → x n ∈ Y := fun n hn =>
    natCast_lt_vExitTime_iff.1 (hlt n hn) n le_rfl
  obtain ⟨p, hps, hsp, hrest⟩ := hx s t hst htg ht
  have hpY : x p ∈ Y := hmemY p (by omega)
  have hδs : dist (v (x s)) (v (x p)) ≤ δ := hA _ hpY _ hsp
  have hJ0 : 0 ≤ J := le_trans dist_nonneg (hjump s (hlt s hst))
  have hδ0 : 0 ≤ δ := le_trans dist_nonneg hδs
  rcases hrest with htp | ⟨q, hsq, hqt, hq1, -, hlast⟩
  · have hδt : dist (v (x p)) (v (x t)) ≤ δ := by
      rw [dist_comm]
      exact hA _ hpY _ htp
    calc dist (v (x s)) (v (x t)) ≤ dist (v (x s)) (v (x p)) + dist (v (x p)) (v (x t)) :=
          dist_triangle _ _ _
      _ ≤ δ + δ := add_le_add hδs hδt
      _ ≤ 3 * δ + J := by linarith
  · have hpq : dist (v (x p)) (v (x (q - 1))) ≤ δ := by
      rw [dist_comm]
      exact hA _ hpY _ hq1
    have hstep : dist (v (x (q - 1))) (v (x q)) ≤ J := by
      have h := hjump (q - 1) (hlt (q - 1) (by omega))
      rwa [Nat.sub_add_cancel (by omega : 1 ≤ q)] at h
    have hsq' : dist (v (x s)) (v (x q)) ≤ 2 * δ + J := by
      calc dist (v (x s)) (v (x q))
          ≤ dist (v (x s)) (v (x p)) + dist (v (x p)) (v (x (q - 1))) +
            dist (v (x (q - 1))) (v (x q)) := dist_triangle4 _ _ _ _
        _ ≤ δ + δ + J := add_le_add (add_le_add hδs hpq) hstep
        _ = 2 * δ + J := by ring
    rcases lt_or_eq_of_le hqt with hqt' | hqt'
    · have hlast' : x t ∈ A (x q) := by
        rcases hlast with h | h
        · omega
        · exact h
      have hδt : dist (v (x q)) (v (x t)) ≤ δ := by
        rw [dist_comm]
        exact hA _ (hmemY q hqt') _ hlast'
      calc dist (v (x s)) (v (x t)) ≤ dist (v (x s)) (v (x q)) + dist (v (x q)) (v (x t)) :=
            dist_triangle _ _ _
        _ ≤ (2 * δ + J) + δ := add_le_add hsq' hδt
        _ = 3 * δ + J := by ring
    · rw [← hqt']
      linarith

/-- **No short travel of the walk in the plane (BG20 Proposition 6.5).**  Let `P_a [τ_Y ≤ σ_K] ≥ 1 - ψ₀`
(the bound (6.36)) and let the exit time from `A y` be shorter than `g` with probability at most `q`
from every `y ∈ Y` (Lemma 6.11).  If every region `A y` with `y ∈ Y` lies in the closed `v`-ball of
radius `δ` about `v y` and every edge of `m` out of a vertex of `Y` has `v`-length at most `J`, then the
walk started at `a` travels `v`-distance more than `3 δ + J` in fewer than `g` steps before `τ_Y` with
probability at most `ψ₀ + K q`. -/
theorem srwLaw_exists_shortTravel_le (m : ℤ → ℤ → ℕ) (a : ℤ) (A : ℤ → Set ℤ) (Y : Set ℤ)
    (g K : ℕ) (v : ℤ → ℂ) {δ J : ℝ} {ψ₀ q : ℝ≥0∞}
    (h0 : srwLaw m a {x | ¬ vExitTime Y x ≤ succExit A K x} ≤ ψ₀)
    (hq : ∀ y ∈ Y, srwLaw m y {z | vExitTime (A y) z < (g : ℕ∞)} ≤ q)
    (hA : ∀ y ∈ Y, ∀ z ∈ A y, dist (v z) (v y) ≤ δ)
    (hJ : ∀ y ∈ Y, ∀ z, m y z ≠ 0 → dist (v y) (v z) ≤ J) (hJ0 : 0 ≤ J) :
    srwLaw m a {x | ∃ s t : ℕ, s < t ∧ t < s + g ∧ (t : ℕ∞) ≤ vExitTime Y x ∧
      3 * δ + J < dist (v (x s)) (v (x t))} ≤ ψ₀ + (K : ℝ≥0∞) * q := by
  have hsub : ∀ᵐ x ∂srwLaw m a,
      x ∈ {x : ℕ → ℤ | ∃ s t : ℕ, s < t ∧ t < s + g ∧ (t : ℕ∞) ≤ vExitTime Y x ∧
        3 * δ + J < dist (v (x s)) (v (x t))} → x ∈ {x | ¬ NoShortTravel A Y g x} := by
    filter_upwards [FrontierSeparation.ae_srwStep_legal m a] with x hleg hx
    obtain ⟨s, t, hst, htg, ht, hgt⟩ := hx
    intro hnst
    refine absurd (dist_le_of_noShortTravel hA (fun n hn => ?_) hnst hst htg ht) (not_le.2 hgt)
    have hnY : x n ∈ Y := natCast_lt_vExitTime_iff.1 hn n le_rfl
    rcases hleg n with h | h
    · rw [h, dist_self]
      exact hJ0
    · exact hJ _ hnY _ h
  exact le_trans (measure_mono_ae hsub) (srwLaw_not_noShortTravel_le m a A Y g K h0 hq)

end MatedCRT.FirstPass.Derived
