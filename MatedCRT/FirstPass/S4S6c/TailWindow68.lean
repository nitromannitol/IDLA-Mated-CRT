import MatedCRT.FirstPass.S4S6c.TailBound68
import MatedCRT.FirstPass.S4S6c.WindowStop68

/-!
# The tail bound of the printed Lemma 6.8 with a centre gate (q2, task fp-S4S6c; LEMMA68 C3, D1-D2)

`TailBound68.printed68_tail_bound` needs the availability `x k ∈ Y` on every state of `S N`, including walks that are
not legal trajectories, where the geometry of LEMMA68 gives no information. Here the gate is built into the test region:
`Wt y` and `Aof y` are the window and the region of the test at `y`, and the one-test bound is required for every centre
`y`, so a non-available centre is given the empty test (`Aof y = ∅`, `Wt y = univ`, see `unavailable_test_empty`). The
geometric inputs are needed only on `Good` (the legal trajectories of quenched probability one): finiteness of the test
starts, availability of the visited centres (`hYvis`), and window containment `Wt y ⊆ U` for available `y`
(`hWU`, `hAof`). The availability and containment conclusion `hwin` is `WindowStop68.window_before_exit_U`.
-/

open MeasureTheory Set Function
open scoped ENNReal

namespace MatedCRT
namespace TailWindow68

open MatedCRT.SuccessiveExitStop MatedCRT.AmplCutoff

/-- A test whose centre is not available is empty: with the window `univ` the exit time is `⊤`, so every time
`n` is before the exit, and the empty region is never met at time `0`. -/
theorem stayInRegionOf_of_not_mem {Wt Aof : ℤ → Set ℤ} {Y : Set ℤ} (hAY : ∀ y ∉ Y, Aof y = ∅)
    (hWY : ∀ y ∉ Y, Wt y = univ) (y : ℤ) (hy : y ∉ Y) : stayInRegionOf Wt Aof y = ∅ := by
  ext w
  rw [mem_empty_iff_false, iff_false]
  intro h
  have h' : ∀ n : ℕ, (n : ℕ∞) < vExitTime (Wt y) w → w n ∈ Aof y := h
  have hlt : ((0 : ℕ) : ℕ∞) < vExitTime (Wt y) w := by
    rw [hWY y hy]
    exact lt_vExitTime_iff.2 (fun k _ => mem_univ _)
  have h0 := h' 0 hlt
  rw [hAY y hy] at h0
  simp at h0

/-- **The tail bound of the printed Lemma 6.8 with the centre gate.** The walk started at `a` stays in `A` until it
exits `U` with probability at most `1/2`. Hypotheses: the one-test bound `hc` for every centre (for the unavailable ones
it is trivial), finiteness of the `N` test starts on `Good`, availability of the visited centres on `Good`, and window
containment `Wt y ⊆ U` and `Aof y = A` for the available centres `y ∈ Y`. -/
theorem printed68_tail_bound_window (m : ℤ → ℤ → ℕ) (a : ℤ) (Wt Aof : ℤ → Set ℤ) (A U Y : Set ℤ)
    (τ : ℕ → (ℕ → ℤ) → ℕ∞) (S : ℕ → Set (ℕ → ℤ))
    (hτ0 : ∀ x, τ 0 x = 0)
    (hτsucc : ∀ (N : ℕ) (x : ℕ → ℤ) (i : ℕ), τ N x = (i : ℕ∞) →
      τ (N + 1) x = (i : ℕ∞) + vExitTime (Wt (x i)) (pathShift i x))
    (hτtop : ∀ N x, τ N x = ⊤ → τ (N + 1) x = ⊤)
    (hS0 : S 0 = univ)
    (hSsucc : ∀ N, S (N + 1) = S N ∩ {x | ∃ k : ℕ, τ N x = k ∧ pathShift k x ∈ stayInRegionOf Wt Aof (x k)})
    {q0 ζ r : ℝ} (hq0 : 0 < q0) (hq0' : q0 ≤ 1) (hζ : 0 < ζ) (hζ' : ζ < 1 / 2)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hrA : r ≤ (q0 / 200 * ζ ^ 2 / (16 * Real.log 2)) ^ (2 / ζ))
    (hc : ∀ y, srwLaw m y (stayInRegionOf Wt Aof y) ≤
      ENNReal.ofReal (1 - q0 / (1 + Real.log (1 / r)) ^ 2))
    (N : ℕ) (hN : r ^ (-ζ) / 200 ≤ N)
    (Good : Set (ℕ → ℤ)) (hGood : srwLaw m a Goodᶜ = 0)
    (hfin : ∀ x ∈ Good, ∀ j < N, τ j x ≠ ⊤)
    (hYvis : ∀ x ∈ Good, ∀ j < N, ∀ k : ℕ, τ j x = k → x k ∈ Y)
    (hWU : ∀ y ∈ Y, Wt y ⊆ U)
    (hAof : ∀ y ∈ Y, Aof y = A) :
    srwLaw m a {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime U x → x n ∈ A} ≤ ENNReal.ofReal (1 / 2) := by
  have hL : 0 ≤ Real.log (1 / r) := Real.log_nonneg (one_le_one_div hr hr1)
  have hP : 1 ≤ (1 + Real.log (1 / r)) ^ 2 := by nlinarith
  have hq1 : q0 / (1 + Real.log (1 / r)) ^ 2 ≤ 1 :=
    le_trans (div_le_self hq0.le hP) hq0'
  have h0q : (0 : ℝ) ≤ 1 - q0 / (1 + Real.log (1 / r)) ^ 2 := by linarith
  -- availability and window containment on `Good` (WindowStop68)
  have hwin := WindowStop68.window_before_exit_U hτ0 hτsucc hfin hYvis hWU
  -- the walk stays in `A` until the exit of `U` only if every test window stays in `A`
  have hstay : ∀ j ≤ N, ∀ x ∈ Good, (∀ n : ℕ, (n : ℕ∞) < vExitTime U x → x n ∈ A) → x ∈ S j := by
    intro j
    induction j with
    | zero =>
      intro _ x _ _
      rw [hS0]
      exact mem_univ x
    | succ j ih =>
      intro hj x hx hstay'
      have hxS : x ∈ S j := ih (by omega) x hx hstay'
      obtain ⟨k, hk, hwk⟩ := hwin x hx j (by omega)
      rw [hSsucc j]
      refine ⟨hxS, k, hk, ?_⟩
      intro n hn
      rw [hAof (x k) (hYvis x hx j (by omega) k hk)]
      exact hstay' (k + n) (hwk n hn)
  have hsub : {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime U x → x n ∈ A} ⊆ Goodᶜ ∪ S N := by
    intro x hx
    by_cases hg : x ∈ Good
    · exact Or.inr (hstay N le_rfl x hg hx)
    · exact Or.inl hg
  have hSN : srwLaw m a (S N) ≤ ENNReal.ofReal (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N :=
    srwLaw_successive_exit_le_pow_Of m a Wt Aof τ S hτ0 hτsucc hτtop hS0 hSsucc
      (Y := (Set.univ : Set ℤ)) (fun y _ => hc y) (fun _ _ _ _ _ => Set.mem_univ _) N
  have hpow : ENNReal.ofReal (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N ≤
      ENNReal.ofReal (Real.exp (-(q0 / (1 + Real.log (1 / r)) ^ 2 * N))) := by
    rw [← ENNReal.ofReal_pow h0q]
    exact ENNReal.ofReal_le_ofReal (TailBound68.one_sub_pow_le_exp_neg hq1 N)
  have hcut := TailBound68.exp_tail_le_cutoff hq0 hr hr1 N hN
  have hhalf := amplification_cutoff (c := q0 / 200) (by linarith) hζ hζ' hr hr1 hrA
  have hexp : ENNReal.ofReal (Real.exp (-(q0 / (1 + Real.log (1 / r)) ^ 2 * N))) ≤ ENNReal.ofReal (1 / 2) :=
    ENNReal.ofReal_le_ofReal (le_trans hcut hhalf)
  calc srwLaw m a {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime U x → x n ∈ A}
      ≤ srwLaw m a (Goodᶜ ∪ S N) := measure_mono hsub
    _ ≤ srwLaw m a Goodᶜ + srwLaw m a (S N) := measure_union_le _ _
    _ = srwLaw m a (S N) := by rw [hGood, zero_add]
    _ ≤ ENNReal.ofReal (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N := hSN
    _ ≤ ENNReal.ofReal (Real.exp (-(q0 / (1 + Real.log (1 / r)) ^ 2 * N))) := hpow
    _ ≤ ENNReal.ofReal (1 / 2) := hexp

#print axioms MatedCRT.TailWindow68.printed68_tail_bound_window

end TailWindow68
end MatedCRT
