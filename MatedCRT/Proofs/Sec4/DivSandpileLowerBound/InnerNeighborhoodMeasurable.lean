import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.InnerNeighborhood
import MatedCRT.Proofs.Measurability.BoundaryLayer

/-! # Measurability of inner-neighbourhood point tests -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology

/-- The exterior-ball test has a null-measurable event when the random set is
null measurable at each point of the fixed countable dense sequence. -/
theorem nullMeasurableSet_exteriorBallTest {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Ω → Set ℂ)
    (hmem : ∀ j, NullMeasurableSet {ω | densePoint j ∈ U ω} P) (e k : ℕ) :
    NullMeasurableSet {ω | exteriorBallTest (U ω) e k} P := by
  have h : ∀ j, NullMeasurableSet {ω | densePoint j ∈ ball (densePoint e)
      (1 / ((k : ℝ) + 1)) → densePoint j ∉ U ω} P := by
    intro j
    by_cases hj : densePoint j ∈ ball (densePoint e) (1 / ((k : ℝ) + 1))
    · convert (hmem j).compl using 1
      ext ω
      simp only [hj, true_implies, mem_ofPred_eq, mem_compl_iff]
    · simp only [hj, false_implies, ofPred_true]
      exact MeasurableSet.univ.nullMeasurableSet
  simpa only [exteriorBallTest, ofPred_forall] using NullMeasurableSet.iInter h

/-- For a random regular-open set, fixed-point membership in its positive
inner neighbourhood is null measurable from the countable trace. -/
theorem nullMeasurableSet_mem_innerNbhd_of_trace {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Ω → Set ℂ)
    (hreg : ∀ᵐ ω ∂P, interior (closure (U ω)) = U ω)
    (hmem : ∀ j, NullMeasurableSet {ω | densePoint j ∈ U ω} P)
    {δ : ℝ} (hδ : 0 < δ) (x : ℂ) :
    NullMeasurableSet {ω | x ∈ innerNbhd δ (U ω)} P := by
  have hex : ∀ e k : ℕ, NullMeasurableSet {ω | exteriorBallTest (U ω) e k ∧
      x ∈ ball (densePoint e) δ} P := by
    intro e k
    by_cases hx : x ∈ ball (densePoint e) δ
    · simpa only [hx, and_true] using nullMeasurableSet_exteriorBallTest P U hmem e k
    · simp only [hx, and_false, ofPred_false]
      exact MeasurableSet.empty.nullMeasurableSet
  have hm := (NullMeasurableSet.iUnion fun e => NullMeasurableSet.iUnion (hex e)).compl
  apply hm.congr
  filter_upwards [hreg] with ω hω
  apply propext
  simp only [mem_compl_iff, mem_iUnion, mem_ofPred_eq]
  rw [innerNbhd_eq_infEDist_superlevel hδ]
  simp only [mem_ofPred_eq, ← not_lt, infEDist_compl_lt_iff_exists_exteriorBallTest hω]

/-- Fixed-point inner-neighbourhood membership for a cone harmonic-ball
family follows from null-measurable membership on the dense trace. -/
theorem nullMeasurableSet_mem_coneFamily_innerNbhd_of_trace
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (Λ : Ω → ℝ → Set ℂ) (t : ℝ) (ht : 0 < t)
    (hΛ : ∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω))
    (hmem : ∀ j, NullMeasurableSet {ω | densePoint j ∈ Λ ω t} P)
    {δ : ℝ} (hδ : 0 < δ) (x : ℂ) :
    NullMeasurableSet {ω | x ∈ innerNbhd δ (Λ ω t)} P := by
  apply nullMeasurableSet_mem_innerNbhd_of_trace P (fun ω => Λ ω t) ?_ hmem hδ x
  filter_upwards [hΛ] with ω hω
  exact hω.2.1.isRegularOpen t ht

end MatedCRT
