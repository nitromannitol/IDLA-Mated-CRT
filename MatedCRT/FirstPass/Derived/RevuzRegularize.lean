import MatedCRT.External.RevuzTimeChange

/-!
# The rational-time regularization of a functional: monotonicity and measurability

`MatedCRT.regularize A` replaces a family `A t : ContinuousPath ℂ → ℝ≥0` by the right-continuous rational-time
regularization used in the explicit Revuz measure `MatedCRT.revuz`.  For every path the regularization is monotone in
`t` (`regularize_monotone`), and for every `t` it is a measurable functional of the path when all `A t` are
(`measurable_regularize`).  These two facts, together with the occupation-kernel lemma of the library, make
`ω ↦ occupationMeasure (regularize A · ω) ω` a measurable map into `Measure ℂ`.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess

/-- Every nonnegative real is bounded above by a nonnegative rational. -/
theorem exists_nnrat_gt_nnreal (t : ℝ≥0) : ∃ q : ℚ≥0, t < (q : ℝ≥0) := by
  obtain ⟨q, hq⟩ := exists_rat_gt (t : ℝ)
  have hq0 : 0 ≤ q := by
    have : (0 : ℝ) ≤ t := t.coe_nonneg
    exact_mod_cast this.trans hq.le
  refine ⟨⟨q, hq0⟩, ?_⟩
  exact_mod_cast hq

/-- The index set of the infimum in `regularize` is nonempty. -/
theorem nonempty_regularize_index (t : ℝ≥0) : Nonempty {q : ℚ≥0 // t < (q : ℝ≥0)} :=
  let ⟨q, hq⟩ := exists_nnrat_gt_nnreal t
  ⟨⟨q, hq⟩⟩

/-- For every path, the regularization is nondecreasing in time. -/
theorem regularize_monotone (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (ω : ContinuousPath ℂ) :
    Monotone fun t => regularize A t ω := by
  intro s t hst
  have hne := nonempty_regularize_index t
  unfold regularize
  split_ifs with h
  · refine le_ciInf fun q => ?_
    exact ciInf_le (OrderBot.bddBelow _) (⟨q.1, hst.trans_lt q.2⟩ : {q : ℚ≥0 // s < (q : ℝ≥0)})
  · exact le_rfl

/-- The regularization of a family of measurable functionals is measurable in the path. -/
theorem measurable_regularize {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : ∀ t, Measurable (A t)) (t : ℝ≥0) :
    Measurable (regularize A t) := by
  classical
  unfold regularize
  refine Measurable.ite ?_ (Measurable.iInf fun q => hA _) measurable_const
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun p => MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ =>
    measurableSet_le (hA _) (hA _)

end MatedCRT
