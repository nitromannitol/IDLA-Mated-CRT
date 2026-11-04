import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ConditionalCutoff

/-! Qualitative radius bounds on the exit-time event. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set

/-- Initial rescaled odometer control on an event transfers to the shell
radius scale on the same event. -/
theorem tendsToOneOn_initialRadius_of_rescaled_odometer
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (F : Set Ω)
    (O : ℝ → Ω → ℝ) (K α : ℝ) (hK : 0 ≤ K) (hα : 0 < α)
    (G : ℝ → Set Ω) (hG : ProbTendsToOne P G)
    (hnonneg : ∀ ε ω, ω ∈ G ε → 0 ≤ O ε ω)
    (hsmall : ∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω | ε * O ε ω ≤ a})) :
    ∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω | (O ε ω * (ε * K)) ^ α ≤ a}) := by
  classical
  let Y : ℝ → Ω → ℝ := fun ε ω => if ω ∈ F then O ε ω else 0
  have hY : ∀ a : ℝ, 0 < a → ProbTendsToOne P (fun ε => {ω | ε * Y ε ω ≤ a}) := by
    intro a ha
    have h := (probTendsToOne_compl_union_iff P F (fun ε => {ω | ε * O ε ω ≤ a})).2
      (hsmall a ha)
    apply h.mono_ev
    filter_upwards with ε ω hω
    rcases hω with hω | hω
    · simp only [mem_compl_iff] at hω
      simp [Y, hω, ha.le]
    · by_cases hF : ω ∈ F
      · simpa [Y, hF] using hω
      · simp [Y, hF, ha.le]
  have hGY : ProbTendsToOne P (fun ε => Fᶜ ∪ G ε) := hG.mono_ev
    (Filter.Eventually.of_forall (fun _ _ hω => Or.inr hω))
  have hYnonneg : ∀ ε ω, ω ∈ Fᶜ ∪ G ε → 0 ≤ Y ε ω := by
    intro ε ω hω
    by_cases hF : ω ∈ F
    · have hGω : ω ∈ G ε := hω.resolve_left (by simpa using hF)
      simpa [Y, hF] using hnonneg ε ω hGω
    · simp [Y, hF]
  have hout := probTendsToOne_initialRadius_of_rescaled_odometer P Y K α hK hα
    (fun ε => Fᶜ ∪ G ε) hGY hYnonneg hY
  intro a ha
  apply (probTendsToOne_compl_union_iff P F (fun ε => {ω | (O ε ω * (ε * K)) ^ α ≤ a})).1
  apply (hout a ha).mono_ev
  filter_upwards with ε ω hω
  by_cases hF : ω ∈ F
  · right
    simpa [Y, hF] using hω
  · exact Or.inl hF

end MatedCRT.Sec7
