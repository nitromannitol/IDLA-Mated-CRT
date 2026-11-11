import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGap

/-! # A contact point inside the interior of a closure -/

namespace MatedCRT

open Set

/-- Continuity and nonnegativity do not imply strict positivity on the interior
of the closure of the positivity set. The example also has continuous nonnegative
uniform approximations which vanish in a neighbourhood of the contact point. -/
theorem continuous_gap_counterexample :
    ∃ f : ℝ → ℝ, Continuous f ∧ (∀ x, 0 ≤ f x) ∧
      (0 : ℝ) ∈ interior (closure {x | 0 < f x}) ∧ f 0 = 0 ∧
      ∀ δ : ℝ, 0 < δ → ∃ g : ℝ → ℝ, Continuous g ∧
        (∀ x, 0 ≤ g x) ∧ (∀ x, |g x - f x| ≤ δ) ∧
        (∀ x, x ^ 2 ≤ δ → g x = 0) := by
  let f : ℝ → ℝ := fun x => x ^ 2
  have hset : {x : ℝ | 0 < f x} = {0}ᶜ := by
    ext x
    simp [f, sq_pos_iff]
  refine ⟨f, continuous_id.pow 2, fun x => sq_nonneg x, ?_, by simp [f], ?_⟩
  · rw [hset, closure_compl_singleton, interior_univ]
    exact mem_univ _
  · intro δ hδ
    let g : ℝ → ℝ := fun x => max 0 (x ^ 2 - δ)
    refine ⟨g, continuous_const.max ((continuous_id.pow 2).sub continuous_const),
      fun x => le_max_left _ _, ?_, ?_⟩
    · intro x
      dsimp [f, g]
      rcases le_total (x ^ 2) δ with hx | hx
      · rw [max_eq_left (by linarith)]
        rw [abs_of_nonpos (by nlinarith [sq_nonneg x])]
        linarith
      · rw [max_eq_right (by linarith)]
        rw [abs_of_nonpos (by linarith)]
        linarith
    · intro x hx
      dsimp [g]
      exact max_eq_left (by linarith)

end MatedCRT
