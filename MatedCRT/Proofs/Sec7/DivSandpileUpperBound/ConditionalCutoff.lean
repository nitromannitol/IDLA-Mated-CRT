import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.InitialScale

/-! Conditional qualitative comparisons for the exit-time event. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set

/-- Conditional high probability is unconditional high probability after
adjoining the complement of the conditioning event. -/
theorem probTendsToOne_compl_union_iff
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : Set Ω) (E : ℝ → Set Ω) :
    ProbTendsToOne P (fun ε => Fᶜ ∪ E ε) ↔ TendsToOneOn P F E := by
  simp only [ProbTendsToOne, TendsToOneOn, compl_union, compl_compl]

/-- On any event, a scale converging to zero in probability eventually falls
below a positive measurable random cutoff in probability. -/
theorem tendsToOneOn_random_le_positive_cutoff
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (F : Set Ω) (dd : Ω → ℝ) (hdd : Measurable dd) (hpos : ∀ ω, 0 < dd ω)
    (X : ℝ → Ω → ℝ)
    (hX : ∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω | X ε ω ≤ a})) :
    TendsToOneOn P F (fun ε => {ω | X ε ω ≤ dd ω}) := by
  classical
  let Y : ℝ → Ω → ℝ := fun ε ω => if ω ∈ F then X ε ω else 0
  have hY : ∀ a : ℝ, 0 < a → ProbTendsToOne P (fun ε => {ω | Y ε ω ≤ a}) := by
    intro a ha
    have h := (probTendsToOne_compl_union_iff P F (fun ε => {ω | X ε ω ≤ a})).2 (hX a ha)
    apply h.mono_ev
    filter_upwards with ε ω hω
    rcases hω with hω | hω
    · simp only [mem_compl_iff] at hω
      simp [Y, hω, ha.le]
    · by_cases hF : ω ∈ F
      · simpa [Y, hF] using hω
      · simp [Y, hF, ha.le]
  have hcut := probTendsToOne_random_le_positive_cutoff P dd hdd hpos Y hY
  apply (probTendsToOne_compl_union_iff P F (fun ε => {ω | X ε ω ≤ dd ω})).1
  apply hcut.mono_ev
  filter_upwards with ε ω hω
  by_cases hF : ω ∈ F
  · right
    simpa [Y, hF] using hω
  · exact Or.inl hF

end MatedCRT.Sec7
