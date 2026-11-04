import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.RadiusCutoff

/-! Comparison with a positive random cutoff under qualitative convergence. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set

/-- A random scale tending to zero in probability is eventually below every
positive measurable random cutoff in probability. No independence is needed. -/
theorem probTendsToOne_random_le_positive_cutoff
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (dd : Ω → ℝ) (hdd : Measurable dd) (hpos : ∀ ω, 0 < dd ω)
    (X : ℝ → Ω → ℝ)
    (hX : ∀ a : ℝ, 0 < a → ProbTendsToOne P (fun ε => {ω | X ε ω ≤ a})) :
    ProbTendsToOne P (fun ε => {ω | X ε ω ≤ dd ω}) := by
  let A : ℕ → Set Ω := fun n => {ω | dd ω < 1 / ((n : ℝ) + 1)}
  have hanti : Antitone A := by
    intro i j hij ω hω
    simp only [A, mem_ofPred_eq] at hω ⊢
    refine hω.trans_le (one_div_le_one_div_of_le (by positivity) ?_)
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    linarith
  have hlim := tendsto_measure_iInter_atTop (μ := P)
    (fun n => (measurableSet_lt hdd measurable_const).nullMeasurableSet) hanti
    ⟨0, measure_ne_top P _⟩
  have hempty : (⋂ n, A n) = ∅ := by
    ext ω
    simp only [A, mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hpos ω)
    exact ⟨n, hn.le⟩
  rw [hempty, measure_empty] at hlim
  unfold ProbTendsToOne
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  obtain ⟨n, hn⟩ := (ENNReal.tendsto_nhds_zero.1 hlim _ he2).exists
  have ha : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hx := ENNReal.tendsto_nhds_zero.1 (hX _ ha) _ he2
  filter_upwards [hx] with ε hε
  calc
    P {ω | X ε ω ≤ dd ω}ᶜ ≤ P (A n) + P {ω | X ε ω ≤ 1 / ((n : ℝ) + 1)}ᶜ := by
      refine (measure_mono ?_).trans (measure_union_le _ _)
      intro ω hω
      simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hω
      by_cases hddn : dd ω < 1 / ((n : ℝ) + 1)
      · exact Or.inl hddn
      · right
        simp only [mem_compl_iff, mem_ofPred_eq, not_le]
        exact (le_of_not_gt hddn).trans_lt hω
    _ ≤ e / 2 + e / 2 := add_le_add hn hε
    _ = e := ENNReal.add_halves e

end MatedCRT.Sec7
