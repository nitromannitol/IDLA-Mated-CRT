import MatedCRT.FirstPass.Derived.OnlyMergeTransfer

/-! # Null measurability of the mating fibre relation -/

open MeasureTheory Set
open MatedCRTHarmonic.MatedCRT

namespace MatedCRT.FirstPass.Derived

/-- The pairs for which the mating relation equals the curve's fibre relation
are null measurable under any finite measure on the joint path space. -/
theorem nullMeasurableSet_matingRel_eq_fibre
    (μ : Measure (C(ℝ, ℂ) × Path2)) [IsFiniteMeasure μ] :
    NullMeasurableSet {p : C(ℝ, ℂ) × Path2 |
      matingRel p.2 = fun s t => p.1 s = p.1 t} μ := by
  have hmerge := (LatticeProb.AnalyticSet.nullMeasurableSet μ
    MatedCRTHarmonic.MatedCRT.analyticSet_setOf_not_merge).compl
  have honly := (LatticeProb.AnalyticSet.nullMeasurableSet μ
    analyticSet_setOf_not_onlyMerge).compl
  have heq : {p : C(ℝ, ℂ) × Path2 | matingRel p.2 = fun s t => p.1 s = p.1 t} =
      {p : C(ℝ, ℂ) × Path2 | ∃ s t : ℝ,
        (DirectRel (fun u => lrCoord 0 u p.2) s t ∨
          DirectRel (fun u => lrCoord 1 u p.2) s t) ∧ p.1 s ≠ p.1 t}ᶜ ∩
      {p : C(ℝ, ℂ) × Path2 | ∃ s t : ℝ,
        p.1 s = p.1 t ∧ ¬ matingRel p.2 s t}ᶜ := by
    ext p
    simp only [mem_ofPred_eq, mem_inter_iff, mem_compl_iff]
    constructor
    · intro h
      constructor
      · rintro ⟨s, t, hd, hne⟩
        apply hne
        have hr : matingRel p.2 s t := Relation.EqvGen.rel _ _ hd
        rw [h] at hr
        exact hr
      · rintro ⟨s, t, he, hn⟩
        apply hn
        rw [h]
        exact he
    · rintro ⟨hm, ho⟩
      apply matingRel_eq_fibre_of_merge
      · intro s t hd
        by_contra hn
        exact hm ⟨s, t, hd, hn⟩
      · intro s t he
        by_contra hn
        exact ho ⟨s, t, he, hn⟩
  rw [heq]
  exact hmerge.inter honly

end MatedCRT.FirstPass.Derived
