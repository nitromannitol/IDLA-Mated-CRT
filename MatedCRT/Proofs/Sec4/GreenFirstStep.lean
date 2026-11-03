import MatedCRT.Proofs.Sec4.GreenLaplacian

/-!
# First-step decomposition of exit times and visit counts (path level)

For a path `x : ℕ → ℤ` started in `A` (`x 0 ∈ A`) and its tail `x(· + 1)`:
* `vExitTime_eq_tail_add_one`: `τ_A(x) = τ_A(x(· + 1)) + 1`;
* `visitsTrunc_succ`: the number of visits to `b` before `min(τ_A, N + 1)` is `1{x 0 = b}` plus the number of visits
  of the tail before `min(τ_A, N)`;
* `visitsBeforeExit_eq_iSup`: the visits before `τ_A` are the supremum of the truncated counts.
These are the path identities behind the first-step equation `G_A(a, b) = δ_{ab} + ∑_c p(a, c) G_A(c, b)`, `a ∈ A`
(eq:discrete-green-laplacian, line 797).
-/

namespace MatedCRT

open Set Classical
open scoped ENNReal

variable {A : Set ℤ} {x : ℕ → ℤ}

/-- `τ_A(x) = τ_A(x(· + 1)) + 1` for a path started in `A`. -/
theorem vExitTime_eq_tail_add_one (hx : x 0 ∈ A) : vExitTime A x = vExitTime A (fun n => x (n + 1)) + 1 := by
  unfold vExitTime
  by_cases h : ∃ n, x n ∉ A
  · have h' : ∃ n, x (n + 1) ∉ A := by
      obtain ⟨n, hn⟩ := h
      cases n with
      | zero => exact absurd hx hn
      | succ n => exact ⟨n, hn⟩
    rw [dite_eq_left h, dite_eq_left h']
    have hfind : Nat.find h = Nat.find h' + 1 := by
      refine (Nat.find_eq_iff h).2 ⟨Nat.find_spec h', fun j hj => ?_⟩
      cases j with
      | zero => exact not_not.2 hx
      | succ i => exact Nat.find_min h' (by omega)
    rw [hfind]
    push_cast
    rfl
  · have h' : ¬ ∃ n, x (n + 1) ∉ A := fun ⟨n, hn⟩ => h ⟨n + 1, hn⟩
    rw [dite_eq_right h, dite_eq_right h']
    rfl

/-- The visits to `b` before `min(τ_A, N)`. -/
noncomputable def visitsTrunc (A : Set ℤ) (b : ℤ) (N : ℕ) (x : ℕ → ℤ) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range N, (if (n : ℕ∞) < vExitTime A x ∧ x n = b then 1 else 0)

theorem visitsBeforeExit_eq_iSup (b : ℤ) (x : ℕ → ℤ) :
    visitsBeforeExit A b x = ⨆ N, visitsTrunc A b N x :=
  ENNReal.tsum_eq_iSup_nat

theorem visitsTrunc_mono (b : ℤ) (x : ℕ → ℤ) : Monotone fun N => visitsTrunc A b N x :=
  fun _ _ h => Finset.sum_le_sum_of_subset (Finset.range_mono h)

theorem visitsTrunc_le (b : ℤ) (N : ℕ) (x : ℕ → ℤ) : visitsTrunc A b N x ≤ N := by
  unfold visitsTrunc
  calc ∑ n ∈ Finset.range N, (if (n : ℕ∞) < vExitTime A x ∧ x n = b then (1 : ℝ≥0∞) else 0)
      ≤ ∑ n ∈ Finset.range N, (1 : ℝ≥0∞) := Finset.sum_le_sum fun n _ => by split_ifs <;> simp
    _ = N := by simp

theorem visitsTrunc_of_not_mem (hx : x 0 ∉ A) (b : ℤ) (N : ℕ) : visitsTrunc A b N x = 0 := by
  simp [visitsTrunc, vExitTime_eq_zero hx]

theorem visitsTrunc_zero (b : ℤ) (x : ℕ → ℤ) : visitsTrunc A b 0 x = 0 := by
  simp [visitsTrunc]

/-- First-step decomposition of the truncated visit counts. -/
theorem visitsTrunc_succ (hx : x 0 ∈ A) (b : ℤ) (N : ℕ) :
    visitsTrunc A b (N + 1) x = (if x 0 = b then 1 else 0) + visitsTrunc A b N (fun n => x (n + 1)) := by
  unfold visitsTrunc
  rw [Finset.sum_range_succ', add_comm]
  have h0 : (0 : ℕ∞) < vExitTime A x := by
    rw [vExitTime_eq_tail_add_one hx]
    exact lt_of_lt_of_le zero_lt_one le_add_self
  congr 1
  · simp only [Nat.cast_zero, h0, true_and]
  · refine Finset.sum_congr rfl fun n _ => ?_
    have hlt : ((n + 1 : ℕ) : ℕ∞) < vExitTime A x ↔ (n : ℕ∞) < vExitTime A (fun n => x (n + 1)) := by
      rw [vExitTime_eq_tail_add_one hx]
      generalize vExitTime A (fun n => x (n + 1)) = k
      induction k using ENat.recTopCoe with
      | top => simp
      | coe k =>
        norm_cast
        omega
    simp only [hlt]

end MatedCRT
