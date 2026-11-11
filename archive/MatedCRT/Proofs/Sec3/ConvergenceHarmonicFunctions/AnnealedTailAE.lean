import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnealedTail

/-! Almost-everywhere quenched estimates and annealed outer probability. -/

namespace MatedCRT

open MeasureTheory Set
open scoped ENNReal

/-- The annealed bound is unchanged when the quenched estimate fails on a
null set in addition to the bad environment set. -/
theorem sectionwiseOuterProb_le_measure_add_of_ae_quenched_le
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (κ : Ω → Measure X)
    (hκ : ∀ ω, κ ω univ ≤ 1) (E : Set (Ω × X)) (B : Set Ω) (c : ℝ≥0∞)
    (hgood : ∀ᵐ ω ∂P, ω ∉ B → κ ω (Prod.mk ω ⁻¹' E) ≤ c) :
    sectionwiseOuterProb P κ E ≤ P B + c := by
  let N : Set Ω := {ω | ω ∉ B ∧ ¬ κ ω (Prod.mk ω ⁻¹' E) ≤ c}
  have hN : P N = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hgood] with ω hω
    simp only [N, mem_ofPred_eq, not_and, not_not]
    exact hω
  calc
    sectionwiseOuterProb P κ E ≤ P (B ∪ N) + c := by
      apply sectionwiseOuterProb_le_measure_add_of_quenched_le P κ hκ E (B ∪ N) c
      intro ω hω
      have hB : ω ∉ B := fun h => hω (mem_union_left N h)
      have hN' : ω ∉ N := fun h => hω (mem_union_right B h)
      by_contra h
      exact hN' ⟨hB, h⟩
    _ ≤ P B + c := by
      apply add_le_add_left
      simpa only [hN, add_zero] using (show P (B ∪ N) ≤ P B + P N from measure_union_le B N)

end MatedCRT

#print axioms MatedCRT.sectionwiseOuterProb_le_measure_add_of_ae_quenched_le
