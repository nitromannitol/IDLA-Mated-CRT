import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.OfSteps
import MatedCRT.Proofs.Sec6.IterativeBound.FieldSigma

/-! Positive random cutoffs dominate vanishing deterministic scales. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set

/-- If a measurable random cutoff is positive, a deterministic scale tending
to zero lies below it with probability tending to one. -/
theorem probTendsToOne_le_positive_cutoff
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (dd : Ω → ℝ) (hdd : Measurable dd) (hpos : ∀ ω, 0 < dd ω)
    (scale : ℝ → ℝ) (hscale : Tendsto scale (𝓝[>] 0) (𝓝 0)) :
    ProbTendsToOne P (fun ε => {ω | scale ε ≤ dd ω}) := by
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
  obtain ⟨n, hn⟩ := (ENNReal.tendsto_nhds_zero.1 hlim e he).exists
  have hthreshold : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  filter_upwards [(tendsto_order.1 hscale).2 _ hthreshold] with ε hε
  refine (measure_mono ?_).trans hn
  intro ω hω
  simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hω
  exact hω.trans hε

/-- The cutoff in Lemma 6.8 is field-measurable; validity promotes this to
measurability on the ambient probability space. -/
theorem probTendsToOne_le_field_cutoff
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) [IsFiniteMeasure S.P]
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (dd : Ω → ℝ) (hdd : Measurable[S.fieldSigma] dd) (hpos : ∀ ω, 0 < dd ω)
    (scale : ℝ → ℝ) (hscale : Tendsto scale (𝓝[>] 0) (𝓝 0)) :
    ProbTendsToOne S.P (fun ε => {ω | scale ε ≤ dd ω}) :=
  probTendsToOne_le_positive_cutoff S.P dd (hdd.mono (S.fieldSigma_le hS) le_rfl)
    hpos scale hscale

end MatedCRT.Sec7
