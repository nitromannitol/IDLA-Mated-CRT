import MatedCRT.Draft.Section5

/-! A logical check for the quantifier-order issue in Lemma 5.3.
It does not assert that the actual Green-function estimate has this form. -/
namespace MatedCRT.Audit.StatementsSec3Sec5M1

/-- A witness chosen separately for each positive time need not be uniform in time. -/
theorem time_dependent_witness_not_uniform :
    (∀ t : ℝ, 0 < t → ∃ s : ℝ, 0 < s ∧ s < t) ∧
      ¬ (∃ s : ℝ, 0 < s ∧ ∀ t : ℝ, 0 < t → s < t) := by
  constructor
  · intro t ht
    exact ⟨t / 2, by linarith, by linarith⟩
  · rintro ⟨s, hs, h⟩
    have := h (s / 2) (by linarith)
    linarith

end MatedCRT.Audit.StatementsSec3Sec5M1
