import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.CompactThreshold

/-! # Random distances to complements of regular-open sets -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology

/-- A fixed-point strict distance test is null measurable from the trace of a
random regular-open set, provided its complement is almost surely nonempty. -/
theorem nullMeasurableSet_lt_infDist_compl_of_trace
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : Ω → Set ℂ)
    (hreg : ∀ᵐ ω ∂P, interior (closure (U ω)) = U ω)
    (hne : ∀ᵐ ω ∂P, (U ω)ᶜ.Nonempty)
    (hmem : ∀ j, NullMeasurableSet {ω | densePoint j ∈ U ω} P)
    (q : ℝ) (x : ℂ) : NullMeasurableSet {ω | q < infDist x (U ω)ᶜ} P := by
  by_cases hq : q < 0
  · have heq : {ω | q < infDist x (U ω)ᶜ} = Set.univ := by
      ext ω
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact hq.trans_le infDist_nonneg
    rw [heq]
    exact MeasurableSet.univ.nullMeasurableSet
  · have hq0 : 0 ≤ q := le_of_not_gt hq
    let A : ℕ → Set Ω := fun n => {ω | x ∈ innerNbhd (q + 1 / ((n : ℝ) + 1)) (U ω)}
    have hmeas : ∀ n, NullMeasurableSet (A n) P := by
      intro n
      apply nullMeasurableSet_mem_innerNbhd_of_trace P U hreg hmem
      positivity
    have h := NullMeasurableSet.iUnion hmeas
    apply h.congr
    filter_upwards [hne] with ω hω
    apply propext
    simp only [mem_iUnion, A, mem_ofPred_eq]
    have hiff : ∀ n : ℕ, x ∈ innerNbhd (q + 1 / ((n : ℝ) + 1)) (U ω) ↔
        q + 1 / ((n : ℝ) + 1) ≤ infDist x (U ω)ᶜ := by
      intro n
      rw [innerNbhd_eq_infEDist_superlevel (by positivity)]
      exact ENNReal.ofReal_le_iff_le_toReal (infEDist_ne_top hω)
    simp only [hiff]
    constructor
    · rintro ⟨n, hn⟩
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · intro hqdist
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hqdist)
      exact ⟨n, by linarith⟩

/-- Localized distance tests need regularity and nonempty complement only on
the null-measurable event of interest. -/
theorem nullMeasurableSet_lt_infDist_compl_of_trace_on
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (E : Set Ω)
    (hE : NullMeasurableSet E P) (U : Ω → Set ℂ)
    (hreg : ∀ᵐ ω ∂P, ω ∈ E → interior (closure (U ω)) = U ω)
    (hne : ∀ᵐ ω ∂P, ω ∈ E → (U ω)ᶜ.Nonempty)
    (hmem : ∀ j, NullMeasurableSet {ω | ω ∈ E ∧ densePoint j ∈ U ω} P)
    (q : ℝ) (x : ℂ) : NullMeasurableSet {ω | ω ∈ E ∧ q < infDist x (U ω)ᶜ} P := by
  classical
  let V : Ω → Set ℂ := fun ω => if ω ∈ E then U ω else ∅
  have hvreg : ∀ᵐ ω ∂P, interior (closure (V ω)) = V ω := by
    filter_upwards [hreg] with ω hω
    by_cases hωE : ω ∈ E
    · simpa only [V, ite_eq_left hωE] using hω hωE
    · simp only [V, ite_eq_right hωE, closure_empty, interior_empty]
  have hvne : ∀ᵐ ω ∂P, (V ω)ᶜ.Nonempty := by
    filter_upwards [hne] with ω hω
    by_cases hωE : ω ∈ E
    · simpa only [V, ite_eq_left hωE] using hω hωE
    · simp only [V, ite_eq_right hωE, compl_empty, univ_nonempty]
  have hvmem : ∀ j, NullMeasurableSet {ω | densePoint j ∈ V ω} P := by
    intro j
    convert hmem j using 1
    ext ω
    by_cases hωE : ω ∈ E <;> simp [V, hωE]
  have h := hE.inter (nullMeasurableSet_lt_infDist_compl_of_trace P V hvreg hvne hvmem q x)
  convert h using 1
  ext ω
  by_cases hωE : ω ∈ E <;> simp [V, hωE]

/-- A continuous random function can be tested on the intersection of a
fixed compact set and a random inner neighbourhood by countably many events. -/
theorem nullMeasurableSet_innerNbhd_compact_inequality_on
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (E : Set Ω)
    (hE : NullMeasurableSet E P) (U : Ω → Set ℂ)
    (hreg : ∀ᵐ ω ∂P, ω ∈ E → interior (closure (U ω)) = U ω)
    (hne : ∀ᵐ ω ∂P, ω ∈ E → (U ω)ᶜ.Nonempty)
    (hmem : ∀ j, NullMeasurableSet {ω | ω ∈ E ∧ densePoint j ∈ U ω} P)
    (K : Set ℂ) (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ)
    (G : Ω → ℂ → ℝ) (b : ℝ)
    (hG : ∀ m : ℕ, ∀ x ∈ K, NullMeasurableSet
      {ω | ω ∈ E ∧ b - 1 / ((m : ℝ) + 1) ≤ G ω x} P)
    (hcont : ∀ᵐ ω ∂P, ω ∈ E → ContinuousOn (G ω) K) :
    NullMeasurableSet {ω | ω ∈ E ∧ ∀ x ∈ K, x ∈ innerNbhd δ (U ω) → b ≤ G ω x} P := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense K
  let F : Ω → K → ℝ := fun ω x => infDist x.1 (U ω)ᶜ
  let H : Ω → K → ℝ := fun ω x => G ω x.1
  have hlevel : ∀ n : ℕ, ∀ x ∈ D, NullMeasurableSet
      {ω | ω ∈ E ∧ δ - 1 / ((n : ℝ) + 1) < F ω x} P := by
    intro n x hx
    exact nullMeasurableSet_lt_infDist_compl_of_trace_on P E hE U hreg hne hmem _ x.1
  have hvalue : ∀ m : ℕ, ∀ x ∈ D, NullMeasurableSet
      {ω | ω ∈ E ∧ b - 1 / ((m : ℝ) + 1) ≤ H ω x} P := by
    intro m x hx
    exact hG m x.1 x.2
  have hc : ∀ᵐ ω ∂P, ω ∈ E → Continuous (F ω) ∧ Continuous (H ω) := by
    filter_upwards [hcont] with ω hω hωE
    exact ⟨(continuous_infDist_pt (U ω)ᶜ).comp continuous_subtype_val,
      continuousOn_iff_continuous_domRestrict.mp (hω hωE)⟩
  have hm := nullMeasurableSet_compact_superlevel_inequality_on P E hE F H D hDc hD δ b
    hlevel hvalue hc
  apply hm.congr
  filter_upwards [hne] with ω hω
  apply propext
  constructor
  · rintro ⟨hωE, h⟩
    refine ⟨hωE, ?_⟩
    intro x hx hxin
    apply h ⟨x, hx⟩
    rw [innerNbhd_eq_infEDist_superlevel hδ] at hxin
    exact (ENNReal.ofReal_le_iff_le_toReal (infEDist_ne_top (hω hωE))).mp hxin
  · rintro ⟨hωE, h⟩
    refine ⟨hωE, ?_⟩
    intro x hx
    apply h x.1 x.2
    rw [innerNbhd_eq_infEDist_superlevel hδ]
    exact (ENNReal.ofReal_le_iff_le_toReal (infEDist_ne_top (hω hωE))).mpr hx

end MatedCRT
