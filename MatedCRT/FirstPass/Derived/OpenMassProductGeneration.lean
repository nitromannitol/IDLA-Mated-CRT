import Mathlib

/-!
# Product σ-algebras and generation relative to a set

If the measurable sets of `X` are, relative to a set `L₁`, the preimages under a code `e₁` of measurable
sets (`S ∩ L₁ = e₁ ⁻¹' T ∩ L₁`), and likewise for `Y`, then the measurable sets of `X × Y` are, relative to
`L₁ ×ˢ L₂`, the preimages under `Prod.map e₁ e₂`.  Applied twice, this gives the open-mass coding of
`A × Measure ℂ × B` relative to the locally finite second coordinate.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Set
open scoped ENNReal

/-- Relative generation passes to products. -/
theorem prod_generation_of_relative {X Y X' Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace X'] [MeasurableSpace Y'] (e₁ : X → X') (e₂ : Y → Y') (L₁ : Set X) (L₂ : Set Y)
    (h₁ : ∀ S : Set X, MeasurableSet S → ∃ T : Set X', MeasurableSet T ∧ S ∩ L₁ = e₁ ⁻¹' T ∩ L₁)
    (h₂ : ∀ S : Set Y, MeasurableSet S → ∃ T : Set Y', MeasurableSet T ∧ S ∩ L₂ = e₂ ⁻¹' T ∩ L₂) :
    ∀ S : Set (X × Y), MeasurableSet S → ∃ T : Set (X' × Y'), MeasurableSet T ∧
      S ∩ L₁ ×ˢ L₂ = (Prod.map e₁ e₂) ⁻¹' T ∩ L₁ ×ˢ L₂ := by
  intro S hS
  refine MeasurableSpace.induction_on_inter
    (C := fun S _ => ∃ T : Set (X' × Y'), MeasurableSet T ∧
      S ∩ L₁ ×ˢ L₂ = (Prod.map e₁ e₂) ⁻¹' T ∩ L₁ ×ˢ L₂)
    generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_ S hS
  · exact ⟨∅, MeasurableSet.empty, by simp⟩
  · rintro _ ⟨s₁, hs₁, s₂, hs₂, rfl⟩
    obtain ⟨T₁, hT₁, e1⟩ := h₁ s₁ hs₁
    obtain ⟨T₂, hT₂, e2⟩ := h₂ s₂ hs₂
    refine ⟨T₁ ×ˢ T₂, hT₁.prod hT₂, ?_⟩
    ext ⟨x, y⟩
    have hx := Set.ext_iff.1 e1 x
    have hy := Set.ext_iff.1 e2 y
    simp only [mem_inter_iff, mem_prod, mem_preimage, Prod.map_apply] at hx hy ⊢
    tauto
  · intro t ht ⟨T, hT, h⟩
    refine ⟨Tᶜ, hT.compl, ?_⟩
    ext x
    have hx := Set.ext_iff.1 h x
    simp only [mem_inter_iff, mem_compl_iff, mem_preimage] at hx ⊢
    tauto
  · intro f _ hfm ih
    choose T hT h using ih
    refine ⟨⋃ i, T i, MeasurableSet.iUnion hT, ?_⟩
    ext x
    have hx := fun i => Set.ext_iff.1 (h i) x
    simp only [mem_inter_iff, mem_iUnion, mem_preimage] at hx ⊢
    constructor
    · rintro ⟨⟨i, hi⟩, hL⟩
      exact ⟨⟨i, ((hx i).1 ⟨hi, hL⟩).1⟩, hL⟩
    · rintro ⟨⟨i, hi⟩, hL⟩
      exact ⟨⟨i, ((hx i).2 ⟨hi, hL⟩).1⟩, hL⟩

/-- The coding of `A × Measure ℂ × B` by the open masses of the middle coordinate, relative to the
locally finite middle coordinate. -/
theorem hcomap_prod_openMass {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] (U : ℕ → Set ℂ)
    (hgen : ∀ S : Set (Measure ℂ), MeasurableSet S → ∃ T : Set (ℕ → ℝ≥0∞), MeasurableSet T ∧
      S ∩ {m | IsLocallyFiniteMeasure m} =
        (fun (m : Measure ℂ) (n : ℕ) => m (U n)) ⁻¹' T ∩ {m | IsLocallyFiniteMeasure m}) :
    ∀ S : Set (A × Measure ℂ × B), MeasurableSet S → ∃ T : Set (A × (ℕ → ℝ≥0∞) × B),
      MeasurableSet T ∧
        S ∩ {q | IsLocallyFiniteMeasure q.2.1} =
          (fun q : A × Measure ℂ × B => (q.1, fun n => q.2.1 (U n), q.2.2)) ⁻¹' T ∩
            {q | IsLocallyFiniteMeasure q.2.1} := by
  have hB : ∀ S : Set B, MeasurableSet S → ∃ T : Set B, MeasurableSet T ∧
      S ∩ univ = id ⁻¹' T ∩ univ := fun S hS => ⟨S, hS, by simp⟩
  have hA : ∀ S : Set A, MeasurableSet S → ∃ T : Set A, MeasurableSet T ∧
      S ∩ univ = id ⁻¹' T ∩ univ := fun S hS => ⟨S, hS, by simp⟩
  have h12 := prod_generation_of_relative (fun (m : Measure ℂ) (n : ℕ) => m (U n)) (id : B → B)
    {m | IsLocallyFiniteMeasure m} univ hgen hB
  have h3 := prod_generation_of_relative (id : A → A)
    (Prod.map (fun (m : Measure ℂ) (n : ℕ) => m (U n)) (id : B → B)) univ
    ({m | IsLocallyFiniteMeasure m} ×ˢ (univ : Set B)) hA h12
  intro S hS
  obtain ⟨T, hT, h⟩ := h3 S hS
  refine ⟨T, hT, ?_⟩
  have hL : (univ ×ˢ ({m | IsLocallyFiniteMeasure m} ×ˢ (univ : Set B)) : Set (A × Measure ℂ × B)) =
      {q | IsLocallyFiniteMeasure q.2.1} := by
    ext q; simp
  rw [hL] at h
  exact h

end MatedCRT.FirstPass.Derived
