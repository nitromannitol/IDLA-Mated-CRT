import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ConditionalCutoff
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicInitialBudgetLimit

/-! Qualitative probabilistic control of the logarithmic dyadic budget. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set Metric

/-- A right-continuous limit at zero transfers qualitative convergence in
probability on an event for an eventually nonnegative random scale. -/
theorem tendsToOneOn_right_limit_of_nonnegative
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (F : Set Ω)
    (X : ℝ → Ω → ℝ) (f : ℝ → ℝ) (hf0 : f 0 = 0)
    (hf : Tendsto f (𝓝[>] 0) (𝓝 0))
    (G : ℝ → Set Ω) (hG : ProbTendsToOne P G)
    (hnonneg : ∀ ε ω, ω ∈ G ε → 0 ≤ X ε ω)
    (hX : ∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω | X ε ω ≤ a})) :
    ∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω | f (X ε ω) ≤ a}) := by
  intro a ha
  have hevent : ∀ᶠ x in 𝓝[>] (0 : ℝ), f x < a := hf.eventually (eventually_lt_nhds ha)
  obtain ⟨d, hd, hbound⟩ := Metric.mem_nhdsWithin_iff.mp hevent
  have hs := (probTendsToOne_compl_union_iff P F (fun ε => {ω | X ε ω ≤ d / 2})).2
    (hX _ (by positivity))
  apply (probTendsToOne_compl_union_iff P F _).1
  apply (hG.inter hs).mono_ev
  filter_upwards [] with ε ω hω
  rcases hω.2 with hF | hx
  · exact Or.inl hF
  · right
    change X ε ω ≤ d / 2 at hx
    have hnonneg' := hnonneg ε ω hω.1
    by_cases hx0 : X ε ω = 0
    · simpa [hx0, hf0] using ha.le
    · have hxpos : 0 < X ε ω := lt_of_le_of_ne hnonneg' (Ne.symm hx0)
      have hxball : X ε ω ∈ ball (0 : ℝ) d := by
        rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hxpos]
        linarith
      have hb : f (X ε ω) < a := hbound ⟨hxball, hxpos⟩
      exact hb.le

/-- The qualitative initial-odometer estimate controls the logarithmic term
in the delayed dyadic radius budget on the same event. -/
theorem tendsToOneOn_delayed_dyadic_initial_log_budget
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (F : Set Ω)
    (X : ℝ → Ω → ℝ) {α c : ℝ} (hα : 0 < α) (hc : 0 < c)
    (G : ℝ → Set Ω) (hG : ProbTendsToOne P G)
    (hnonneg : ∀ ε ω, ω ∈ G ε → 0 ≤ X ε ω)
    (hX : ∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω | X ε ω ≤ a})) :
    ∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω |
      (X ε ω) ^ α *
        (1 + |Real.log ((c / 8) * (X ε ω * (1 / 2 : ℝ)) ^ α)| +
          |Real.log ((1 / 2 : ℝ) ^ α)|) ^ 2 ≤ a}) := by
  apply tendsToOneOn_right_limit_of_nonnegative P F X _ ?_
    (tendsto_delayed_dyadic_initial_log_budget hα hc) G hG hnonneg hX
  simp [Real.zero_rpow hα.ne']

end MatedCRT.Sec7
