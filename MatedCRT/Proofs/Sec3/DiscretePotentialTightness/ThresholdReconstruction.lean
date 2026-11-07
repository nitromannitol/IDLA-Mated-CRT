import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.TwoMeshCellEvents

/-! # Measurable reconstruction from threshold events -/

namespace MatedCRT

open Set MeasureTheory

/-- Rational threshold versions determine a measurable version of a bounded
    nonnegative function on an arbitrary event. -/
theorem exists_measurable_version_of_thresholds
    {Ω : Type*} [MeasurableSpace Ω] (P : Ω → Prop) (f : Ω → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hbound : ∀ ω, P ω → 0 ≤ f ω ∧ f ω ≤ C)
    (A : ℚ → Set Ω) (hAm : ∀ q, MeasurableSet (A q))
    (hA : ∀ ω, P ω → ∀ q, (ω ∈ A q ↔ (q : ℝ) < f ω)) :
    ∃ g : Ω → ℝ, Measurable g ∧ ∀ ω, P ω → g ω = f ω := by
  classical
  let z : ℚ → Ω → ℝ := fun q ω =>
    if 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ C ∧ ω ∈ A q then (q : ℝ) else 0
  have hzm : ∀ q, Measurable (z q) := by
    intro q
    by_cases hq : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ C
    · simpa only [z, hq.1, hq.2, true_and] using
        (Measurable.ite (p := fun ω : Ω => ω ∈ A q) (hAm q)
          measurable_const (measurable_const : Measurable (fun _ : Ω => (0 : ℝ))))
    · have hq' : ¬ (0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ C) := hq
      simpa only [z, ← and_assoc, hq', false_and, ite_false] using
        (measurable_const : Measurable (fun _ : Ω => (0 : ℝ)))
  have hz0 : ∀ q ω, 0 ≤ z q ω := by
    intro q ω
    simp only [z]
    split_ifs with h
    · exact h.1
    · exact le_rfl
  have hzC : ∀ q ω, z q ω ≤ C := by
    intro q ω
    simp only [z]
    split_ifs with h
    · exact h.2.1
    · exact hC
  let g : Ω → ℝ := fun ω => ⨆ q : ℚ, z q ω
  refine ⟨g, Measurable.iSup hzm, ?_⟩
  intro ω hP
  have hbdd : BddAbove (range fun q : ℚ => z q ω) := ⟨C, by
    rintro x ⟨q, rfl⟩
    exact hzC q ω⟩
  have hg0 : 0 ≤ g ω := (hz0 0 ω).trans (le_ciSup hbdd 0)
  have hg_le : g ω ≤ f ω := by
    apply ciSup_le
    intro q
    simp only [z]
    split_ifs with h
    · exact ((hA ω hP q).mp h.2.2).le
    · exact (hbound ω hP).1
  apply le_antisymm hg_le
  by_contra h
  have hlt : g ω < f ω := lt_of_not_ge h
  obtain ⟨q, hqg, hqf⟩ := exists_rat_btwn hlt
  have hq0 : 0 ≤ (q : ℝ) := (hg0.trans hqg.le)
  have hqC : (q : ℝ) ≤ C := hqf.le.trans (hbound ω hP).2
  have hqA : ω ∈ A q := (hA ω hP q).mpr hqf
  have hqle : (q : ℝ) ≤ g ω := by
    have hval : z q ω = (q : ℝ) := by
      dsimp only [z]
      split_ifs with h
      · rfl
      · exact False.elim (h ⟨hq0, hqC, hqA⟩)
    rw [← hval]
    exact le_ciSup hbdd q
  exact (not_lt_of_ge hqle) hqg

end MatedCRT
