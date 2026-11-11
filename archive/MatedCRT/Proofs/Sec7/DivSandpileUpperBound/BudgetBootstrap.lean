import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.FiniteStopping

/-! Bootstrap of contraction and the spatial budget before threshold crossing. -/

namespace MatedCRT.Sec7

/-- If contraction holds whenever the accumulated spatial budget is admissible,
the geometric radius bound makes that budget admissible up to the first
threshold crossing. The finite horizon is chosen using the same geometric
majorant. -/
theorem exists_shell_threshold_of_budget_bootstrap
    (O r : ℕ → ℝ) (q K α R D B δ : ℝ) (n : ℕ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hK : 0 ≤ K) (hα : 0 < α)
    (hR : 0 ≤ R) (hD : 0 ≤ D) (hr0 : 0 ≤ r 0) (hO : ∀ k ≤ n, 0 ≤ O k)
    (hend : O 0 * q ^ n ≤ B)
    (hr : ∀ k < n, r (k + 1) ≤ max ((O k * K) ^ α) R)
    (hstep : ∀ k < n, B < O k →
      (∑ j ∈ Finset.range k, r j) + ((k : ℝ) + 1) * (2 * D) ≤ δ →
      (∀ j < k, O (j + 1) ≤ q * O j) →
      O (k + 1) ≤ q * O k)
    (hbudget : r 0 + (O 0 * K) ^ α / (1 - q ^ α) +
      (n : ℝ) * R + ((n : ℝ) + 1) * (2 * D) ≤ δ) :
    ∃ τ : ℕ, τ ≤ n ∧ O τ ≤ B ∧ (∀ k < τ, B < O k) ∧
      (∑ j ∈ Finset.range τ, r j) + ((τ : ℝ) + 1) * (2 * D) ≤ δ := by
  have hA : 0 ≤ (O 0 * K) ^ α / (1 - q ^ α) := by
    apply div_nonneg (Real.rpow_nonneg (mul_nonneg (hO 0 (Nat.zero_le n)) hK) α)
    exact sub_nonneg.mpr (Real.rpow_lt_one hq hq1 hα).le
  have hprefix : ∀ k ≤ n, (∀ j < k, B < O j) →
      (∀ j < k, O (j + 1) ≤ q * O j) ∧
      (∑ j ∈ Finset.range k, r j) + ((k : ℝ) + 1) * (2 * D) ≤ δ := by
    intro k hk
    induction k with
    | zero =>
      intro _
      simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_add]
      constructor
      · intro j hj
        omega
      · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith
    | succ k ih =>
      intro habove
      obtain ⟨hprev, hbudgetprev⟩ := ih (by omega) (fun j hj => habove j (by omega))
      have hnext : O (k + 1) ≤ q * O k :=
        hstep k (by omega) (habove k (by omega)) hbudgetprev hprev
      have hsteps : ∀ j < k + 1, O (j + 1) ≤ q * O j := by
        intro j hj
        by_cases h : j < k
        · exact hprev j h
        · have : j = k := by omega
          simpa [this] using hnext
      refine ⟨hsteps, ?_⟩
      have hsum := shell_radii_sum_from_odometer_contraction O r q K α R k
        hq hq1 hK hα hR (fun j hj => hO j (by omega)) hprev
        (fun j hj => hr j (by omega))
      have hkn : (k : ℝ) ≤ n := by exact_mod_cast (show k ≤ n by omega)
      have hkn' : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hk
      push_cast at hkn'
      push_cast
      nlinarith
  have hex : ∃ k, k ≤ n ∧ O k ≤ B := by
    by_contra h
    have habove : ∀ k ≤ n, B < O k := by
      intro k hk
      exact lt_of_not_ge (fun hle => h ⟨k, hk, hle⟩)
    have hsteps := (hprefix n le_rfl (fun j hj => habove j (by omega))).1
    have hgeom : ∀ k ≤ n, O k ≤ O 0 * q ^ k := by
      intro k hk
      induction k with
      | zero => simp
      | succ k ih =>
        calc
          O (k + 1) ≤ q * O k := hsteps k (by omega)
          _ ≤ q * (O 0 * q ^ k) := mul_le_mul_of_nonneg_left (ih (by omega)) hq
          _ = O 0 * q ^ (k + 1) := by rw [pow_succ]; ring
    exact (not_lt_of_ge ((hgeom n le_rfl).trans hend)) (habove n le_rfl)
  let τ := Nat.find hex
  have hτn : τ ≤ n := (Nat.find_spec hex).1
  have hτ : O τ ≤ B := (Nat.find_spec hex).2
  have hbefore : ∀ k < τ, B < O k := by
    intro k hk
    exact lt_of_not_ge (fun hle => Nat.find_min hex hk ⟨by omega, hle⟩)
  exact ⟨τ, hτn, hτ, hbefore, (hprefix τ hτn hbefore).2⟩

end MatedCRT.Sec7
