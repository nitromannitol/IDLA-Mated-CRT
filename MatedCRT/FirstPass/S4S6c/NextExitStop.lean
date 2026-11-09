import MatedCRT.FirstPass.S4S6c.SuccessiveTests
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Visit

/-!
# LEMMA68 N3c: the stopping property of the concrete test times (q2, task fp-S4S6c; write-up C1-C3)

The successive-test lemma `srwLaw_successive_tests_le_pow` needs, for each test index `N` and time `k`, that the event
`S N ∩ {τ N = k}` is determined by the history `pathHist k`. This file proves the three building blocks:
* `exists_pathHist_of_determinacy`: an event depending only on `pathHist k` is `pathHist k`-measurable (the target
  `Fin (k+1) → ℤ` is countable, so every set is measurable);
* `vExitTime_eq_coe_iff`: `vExitTime A x = m` iff `x_i ∈ A` for `i < m` and `x_m ∉ A`;
* `vExitTime_pathShift_congr`: after a shift `j`, the event `{vExitTime A (pathShift j x) = m}` with `j + m ≤ k` depends only
  on `pathHist k`.
The next exit time `T_{j+1} = T_j + vExitTime (region of x_{T_j}) (pathShift T_j x)` (write-up C1) combines them.
-/

open MeasureTheory Set

namespace MatedCRT

namespace NextExitStop

/-- An event determined by the history up to time `k` is `pathHist k`-measurable. -/
theorem exists_pathHist_of_determinacy (k : ℕ) (P : (ℕ → ℤ) → Prop)
    (hdet : ∀ x y : ℕ → ℤ, pathHist k x = pathHist k y → (P x ↔ P y)) :
    ∃ F : Set (Fin (k + 1) → ℤ), MeasurableSet F ∧ {x | P x} = {x | pathHist k x ∈ F} := by
  refine ⟨pathHist k '' {x | P x}, (Set.to_countable _).measurableSet, ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    exact (hdet y x hxy).1 hy

/-- `vExitTime A x = m` iff the path is in `A` strictly before `m` and leaves `A` at `m`. -/
theorem vExitTime_eq_coe_iff (A : Set ℤ) (w : ℕ → ℤ) (m : ℕ) :
    vExitTime A w = (m : ℕ∞) ↔ (∀ i < m, w i ∈ A) ∧ w m ∉ A := by
  constructor
  · intro h
    have hlt : ∀ i < m, w i ∈ A := by
      intro i hi
      have h1 : (i : ℕ∞) < vExitTime A w := by
        rw [h]
        exact_mod_cast hi
      exact ConstantOrderDiv.lt_vExitTime_iff'.1 h1 i le_rfl
    refine ⟨hlt, fun hm => ?_⟩
    have h2 : (m : ℕ∞) < vExitTime A w := by
      refine ConstantOrderDiv.lt_vExitTime_iff'.2 fun j hj => ?_
      rcases Nat.lt_or_eq_of_le hj with h' | h'
      · exact hlt j h'
      · rw [h']
        exact hm
    rw [h] at h2
    exact absurd h2 (lt_irrefl _)
  · rintro ⟨hlt, hm⟩
    have hnot : ¬ ((m : ℕ∞) < vExitTime A w) := fun h =>
      hm (ConstantOrderDiv.lt_vExitTime_iff'.1 h m le_rfl)
    have hge : (m : ℕ∞) ≤ vExitTime A w := by
      by_contra hlt'
      have hlt'' : vExitTime A w < (m : ℕ∞) := not_le.1 hlt'
      obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hlt'')
      have hjm : j < m := by
        have : (j : ℕ∞) < (m : ℕ∞) := by rw [hj]; exact hlt''
        exact_mod_cast this
      have hjlt : (j : ℕ∞) < vExitTime A w :=
        ConstantOrderDiv.lt_vExitTime_iff'.2 fun l hl => hlt l (lt_of_le_of_lt hl hjm)
      rw [← hj] at hjlt
      exact absurd hjlt (lt_irrefl _)
    exact le_antisymm (not_lt.1 hnot) hge

/-- After a shift `j`, the window event `{vExitTime A (pathShift j x) = m}` with `j + m ≤ k` depends only on `pathHist k`. -/
theorem vExitTime_pathShift_congr (A : Set ℤ) {k j m : ℕ} (hjm : j + m ≤ k) {x y : ℕ → ℤ}
    (hxy : pathHist k x = pathHist k y) :
    vExitTime A (pathShift j x) = (m : ℕ∞) ↔ vExitTime A (pathShift j y) = (m : ℕ∞) := by
  have e : ∀ i ≤ m, x (j + i) = y (j + i) := by
    intro i hi
    have := congrFun hxy ⟨j + i, by omega⟩
    simpa [pathHist] using this
  rw [vExitTime_eq_coe_iff, vExitTime_eq_coe_iff]
  simp only [pathShift]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [← e i hi.le]
      exact h1 i hi
    · rw [← e m le_rfl]
      exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [e i hi.le]
      exact h1 i hi
    · rw [e m le_rfl]
      exact h2

#print axioms MatedCRT.NextExitStop.exists_pathHist_of_determinacy
#print axioms MatedCRT.NextExitStop.vExitTime_eq_coe_iff
#print axioms MatedCRT.NextExitStop.vExitTime_pathShift_congr

end NextExitStop

end MatedCRT
