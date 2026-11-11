import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The Borel graph theorem between standard Borel spaces

General measure theory, not specific to the paper. It is the measurability input of the
measurable decoder in Prop 5.1 (the floor).

A function between standard Borel spaces with Borel graph is Borel (Kechris, *Classical Descriptive Set Theory*, Theorem 14.12).
Proof (Kechris 14.12, from the Lusin–Souslin theorem Kechris 15.1): for a Borel set `B ⊆ Y`, `f⁻¹' B` is the image of the Borel
set `G ∩ (X × B)` under the first projection, where `G` is the graph. The projection is injective on `G`, since `f` is a function.
Its image is Borel by the Lusin–Souslin theorem, which is `MeasurableSet.image_of_measurable_injOn` in Mathlib.
-/

open MeasureTheory

/-- **Borel graph theorem** (Kechris, *Classical Descriptive Set Theory*, Theorem 14.12). A function `f` between standard Borel
spaces whose graph `{(x, f x)}` is measurable in the product σ-algebra is measurable. -/
theorem measurable_of_measurableSet_graph {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] {f : X → Y}
    (hf : MeasurableSet {p : X × Y | f p.1 = p.2}) : Measurable f := by
  intro B hB
  have hS : MeasurableSet ({p : X × Y | f p.1 = p.2} ∩ (Set.univ ×ˢ B)) :=
    hf.inter (MeasurableSet.univ.prod hB)
  have hinj : Set.InjOn Prod.fst ({p : X × Y | f p.1 = p.2} ∩ (Set.univ ×ˢ B)) := by
    rintro ⟨x, y⟩ ⟨hxy, -⟩ ⟨x', y'⟩ ⟨hxy', -⟩ h
    have hxy₁ : f x = y := hxy
    have hxy₂ : f x' = y' := hxy'
    have hx : x = x' := h
    subst hx
    exact Prod.ext rfl (hxy₁.symm.trans hxy₂)
  have himg : Prod.fst '' ({p : X × Y | f p.1 = p.2} ∩ (Set.univ ×ˢ B)) = f ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨⟨a, b⟩, ⟨hab, -, hbB⟩, rfl⟩
      have hab' : f a = b := hab
      show f a ∈ B
      rw [hab']
      exact hbB
    · intro hx
      exact ⟨(x, f x), ⟨rfl, Set.mem_univ _, hx⟩, rfl⟩
  rw [← himg]
  exact MeasurableSet.image_of_measurable_injOn hS measurable_fst hinj
