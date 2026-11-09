import MatedCRT.FirstPass.S4S6c.SuccessiveExitStop
import MatedCRT.Proofs.WalkPotential.ExitBeforeHit

/-!
# Window induction for the printed Lemma 6.8 (q2, task fp-S4S6c; LEMMA68 C3, the windows stay in `U`)

The successive exit-time tests are `τ (N+1) x = τ N x + vExitTime (W (x (τ N x))) (pathShift (τ N x) x)`.
Pure induction on the test index, with no probability: if the test starts of the walk `x` (on a set `Good`) are finite,
each test centre `x k` is available (`x k ∈ Y`), and every available window lies in `U` (`W y ⊆ U` for `y ∈ Y`), then
the walk stays in `U` at every time before the end of the `j`-th test, and before the exit of `U` after the `j`-th test
window. This is the availability-and-containment conclusion `hwin` of `TailBound68.printed68_tail_bound`, derived from
geometric inputs that are only needed on `Good` (the legal trajectories of quenched probability one, LEMMA68 C2).
-/

open MeasureTheory Set Function
open scoped ENNReal

namespace MatedCRT
namespace WindowStop68

/-- A walk lies in `V` at every time strictly before its exit time from `V` (`MatedCRT.lt_vExitTime_iff`). -/
theorem mem_of_lt_vExitTime {V : Set ℤ} {w : ℕ → ℤ} {n : ℕ} (h : (n : ℕ∞) < vExitTime V w) : w n ∈ V :=
  (lt_vExitTime_iff.1 h) n le_rfl

/-- A walk that stays in `V` up to time `M` has exit time larger than `M` (`MatedCRT.lt_vExitTime_iff`). -/
theorem lt_vExitTime_of_forall {V : Set ℤ} {w : ℕ → ℤ} {M : ℕ} (h : ∀ m ≤ M, w m ∈ V) :
    (M : ℕ∞) < vExitTime V w :=
  lt_vExitTime_iff.2 h

/-- **Prefix containment.** On `Good`, if the first `j ≤ N` tests have finite starts, their centres are available
and their windows lie in `U`, then every time before the start `k` of the `j`-th test lies in `U`. -/
theorem prefix_mem_of_tests {W : ℤ → Set ℤ} {U Y : Set ℤ} {τ : ℕ → (ℕ → ℤ) → ℕ∞} {Good : Set (ℕ → ℤ)} {N : ℕ}
    (hτ0 : ∀ x, τ 0 x = 0)
    (hτsucc : ∀ (j : ℕ) (x : ℕ → ℤ) (i : ℕ), τ j x = (i : ℕ∞) →
      τ (j + 1) x = (i : ℕ∞) + vExitTime (W (x i)) (pathShift i x))
    (hfin : ∀ x ∈ Good, ∀ j < N, τ j x ≠ ⊤)
    (hYvis : ∀ x ∈ Good, ∀ j < N, ∀ k : ℕ, τ j x = k → x k ∈ Y)
    (hWU : ∀ y ∈ Y, W y ⊆ U) :
    ∀ j ≤ N, ∀ x ∈ Good, ∀ k : ℕ, τ j x = k → ∀ m < k, x m ∈ U := by
  intro j
  induction j with
  | zero =>
    intro _ x _ k hk m hm
    rw [hτ0 x] at hk
    have hk0 : k = 0 := by exact_mod_cast hk.symm
    omega
  | succ j ih =>
    intro hj x hx k hk m hm
    have hjN : j < N := by omega
    obtain ⟨i, hi⟩ := ENat.ne_top_iff_exists.1 (hfin x hx j hjN)
    rw [hτsucc j x i hi.symm] at hk
    have he : vExitTime (W (x i)) (pathShift i x) ≠ ⊤ := by
      intro htop
      rw [htop, add_top] at hk
      exact ENat.natCast_ne_top k hk.symm
    obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.1 he
    rw [← ht] at hk
    have hik : i + t = k := by exact_mod_cast hk
    by_cases hmi : m < i
    · exact ih (by omega) x hx i hi.symm m hmi
    · have hlt : ((m - i : ℕ) : ℕ∞) < vExitTime (W (x i)) (pathShift i x) := by
        rw [← ht]
        exact_mod_cast (by omega : m - i < t)
      have hmem := mem_of_lt_vExitTime hlt
      have hpe : pathShift i x (m - i) = x m := by
        show x (i + (m - i)) = x m
        congr 1
        omega
      rw [hpe] at hmem
      exact hWU (x i) (hYvis x hx j hjN i hi.symm) hmem

/-- **Window containment.** On `Good`, the `j`-th test (`j < N`) started at `k = τ j x` stays in `U` up to the exit
time of its window, and that exit time is before the exit of `U`: the conclusion `hwin` of the tail bound. -/
theorem window_before_exit_U {W : ℤ → Set ℤ} {U Y : Set ℤ} {τ : ℕ → (ℕ → ℤ) → ℕ∞} {Good : Set (ℕ → ℤ)} {N : ℕ}
    (hτ0 : ∀ x, τ 0 x = 0)
    (hτsucc : ∀ (j : ℕ) (x : ℕ → ℤ) (i : ℕ), τ j x = (i : ℕ∞) →
      τ (j + 1) x = (i : ℕ∞) + vExitTime (W (x i)) (pathShift i x))
    (hfin : ∀ x ∈ Good, ∀ j < N, τ j x ≠ ⊤)
    (hYvis : ∀ x ∈ Good, ∀ j < N, ∀ k : ℕ, τ j x = k → x k ∈ Y)
    (hWU : ∀ y ∈ Y, W y ⊆ U) :
    ∀ x ∈ Good, ∀ j < N, ∃ k : ℕ, τ j x = k ∧
      ∀ n : ℕ, (n : ℕ∞) < vExitTime (W (x k)) (pathShift k x) → ((k + n : ℕ) : ℕ∞) < vExitTime U x := by
  intro x hx j hj
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (hfin x hx j hj)
  refine ⟨k, hk.symm, ?_⟩
  intro n hn
  apply lt_vExitTime_of_forall
  intro m hm
  by_cases hmk : m < k
  · exact prefix_mem_of_tests hτ0 hτsucc hfin hYvis hWU j (le_of_lt hj) x hx k hk.symm m hmk
  · have hlt : ((m - k : ℕ) : ℕ∞) < vExitTime (W (x k)) (pathShift k x) :=
      lt_of_le_of_lt (by exact_mod_cast (by omega : m - k ≤ n)) hn
    have hmem := mem_of_lt_vExitTime hlt
    have hpe : pathShift k x (m - k) = x m := by
      show x (k + (m - k)) = x m
      congr 1
      omega
    rw [hpe] at hmem
    exact hWU (x k) (hYvis x hx j hj k hk.symm) hmem

#print axioms MatedCRT.WindowStop68.prefix_mem_of_tests
#print axioms MatedCRT.WindowStop68.window_before_exit_U

end WindowStop68
end MatedCRT
