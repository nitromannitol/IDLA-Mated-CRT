import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicLevelCrossing

/-! First crossing times for a sequence of decreasing odometer levels. -/

namespace MatedCRT.Sec7

/-- Successive first crossing times. The default value is only used if a
crossing does not exist; the estimates below establish existence in use. -/
noncomputable def levelCrossingTimes (O level : ℕ → ℝ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => by
      classical
      let t := levelCrossingTimes O level j
      exact if h : ∃ k, O (t + k) ≤ level (j + 1) then t + Nat.find h else t

/-- Local crossing estimates produce a coherent sequence of first crossing
times. An overshoot gives equal consecutive times, so skipped levels cost no
shells. -/
theorem levelCrossingTimes_spec
    (O level : ℕ → ℝ) (bound : ℕ → ℝ)
    (h0 : O 0 ≤ level 0)
    (hcross : ∀ j t, O t ≤ level j →
      ∃ d : ℕ, O (t + d) ≤ level (j + 1) ∧ (d : ℝ) ≤ bound j) :
    ∀ j, O (levelCrossingTimes O level j) ≤ level j ∧
      levelCrossingTimes O level j ≤ levelCrossingTimes O level (j + 1) ∧
      ((levelCrossingTimes O level (j + 1) - levelCrossingTimes O level j : ℕ) : ℝ)
        ≤ bound j ∧
      ∀ k < levelCrossingTimes O level (j + 1) - levelCrossingTimes O level j,
        level (j + 1) < O (levelCrossingTimes O level j + k) := by
  have hlevels : ∀ j, O (levelCrossingTimes O level j) ≤ level j := by
    intro j
    induction j with
    | zero => simpa [levelCrossingTimes] using h0
    | succ j ih =>
      obtain ⟨d, hd, _⟩ := hcross j _ ih
      have hex : ∃ k, O (levelCrossingTimes O level j + k) ≤ level (j + 1) := ⟨d, hd⟩
      simpa [levelCrossingTimes, hex] using Nat.find_spec hex
  intro j
  obtain ⟨d, hd, hbound⟩ := hcross j _ (hlevels j)
  have hex : ∃ k, O (levelCrossingTimes O level j + k) ≤ level (j + 1) := ⟨d, hd⟩
  have htime : levelCrossingTimes O level (j + 1) =
      levelCrossingTimes O level j + Nat.find hex := by
    simp [levelCrossingTimes, hex]
  refine ⟨hlevels j, ?_, ?_, ?_⟩
  · rw [htime]
    exact Nat.le_add_right _ _
  · rw [htime, Nat.add_sub_cancel_left]
    exact (Nat.cast_le.mpr (Nat.find_min' hex hd)).trans hbound
  · rw [htime, Nat.add_sub_cancel_left]
    intro k hk
    exact lt_of_not_ge (Nat.find_min hex hk)

end MatedCRT.Sec7
