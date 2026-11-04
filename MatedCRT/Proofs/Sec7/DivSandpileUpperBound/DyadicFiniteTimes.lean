import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicLevelTimes
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicFiniteCrossing

/-! First-crossing times for shell maxima stopped at a finite horizon. -/

namespace MatedCRT.Sec7

/-- If the value at the terminal time lies below every later level, all the
successive first-crossing times remain within the terminal time. -/
theorem levelCrossingTimes_le_terminal
    (O level : ℕ → ℝ) (n : ℕ) (hterminal : ∀ j, O n ≤ level (j + 1)) :
    ∀ j, levelCrossingTimes O level j ≤ n := by
  classical
  intro j
  induction j with
  | zero => simp [levelCrossingTimes]
  | succ j ih =>
    let t := levelCrossingTimes O level j
    have htn : t ≤ n := ih
    have hhit : O (t + (n - t)) ≤ level (j + 1) := by
      rw [Nat.add_sub_of_le htn]
      exact hterminal j
    have hex : ∃ k, O (t + k) ≤ level (j + 1) := ⟨n - t, hhit⟩
    have hfirst : Nat.find hex ≤ n - t := Nat.find_min' hex hhit
    change (if h : ∃ k, O (t + k) ≤ level (j + 1) then t + Nat.find h else t) ≤ n
    simp only [hex, dite_true]
    omega

end MatedCRT.Sec7
