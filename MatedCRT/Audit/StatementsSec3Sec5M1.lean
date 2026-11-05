import MatedCRT.Steps.Sec5.IDLALowerBound

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

/-- The relaxed form of Lemma 5.2 really supplies the Draft statement. -/
theorem relaxed_five_two_implies_draft (𝒮 : SpaceFillingSLEModel)
    (h : GeneralIDLALowerBoundRelaxedStep 𝒮) : GeneralIDLALowerBoundStmt 𝒮 :=
  generalIDLALowerBound_of_relaxed 𝒮 h

#print axioms time_dependent_witness_not_uniform
#print axioms relaxed_five_two_implies_draft

end MatedCRT.Audit.StatementsSec3Sec5M1
